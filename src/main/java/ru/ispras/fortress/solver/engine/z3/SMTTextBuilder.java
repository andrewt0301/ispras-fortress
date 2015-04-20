/*
 * Copyright 2011-2014 ISP RAS (http://www.ispras.ru)
 * 
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 * 
 * http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software distributed under the License
 * is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
 * or implied. See the License for the specific language governing permissions and limitations under
 * the License.
 */

package ru.ispras.fortress.solver.engine.z3;

import static ru.ispras.fortress.solver.engine.smt.SMTStrings.ASSERT;
import static ru.ispras.fortress.solver.engine.smt.SMTStrings.BRACKET_CLOSE;
import static ru.ispras.fortress.solver.engine.smt.SMTStrings.BRACKET_OPEN;
import static ru.ispras.fortress.solver.engine.smt.SMTStrings.CHECK_SAT;
import static ru.ispras.fortress.solver.engine.smt.SMTStrings.DECLARE_CONST;
import static ru.ispras.fortress.solver.engine.smt.SMTStrings.DEFAULT_ARRAY;
import static ru.ispras.fortress.solver.engine.smt.SMTStrings.DEFINE_FUN;
import static ru.ispras.fortress.solver.engine.smt.SMTStrings.EXIT;
import static ru.ispras.fortress.solver.engine.smt.SMTStrings.GET_MODEL;
import static ru.ispras.fortress.solver.engine.smt.SMTStrings.GET_VALUE;
import static ru.ispras.fortress.solver.engine.smt.SMTStrings.PARAM_DEF;
import static ru.ispras.fortress.solver.engine.smt.SMTStrings.SPACE;
import static ru.ispras.fortress.solver.engine.smt.SMTStrings.UNDERLINE;
import static ru.ispras.fortress.solver.engine.smt.SMTStrings.textForData;
import static ru.ispras.fortress.solver.engine.smt.SMTStrings.textForType;

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.DataTypeId;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.data.types.bitvector.BitVector;
import ru.ispras.fortress.expression.ExprTreeVisitor;
import ru.ispras.fortress.expression.ExprTreeWalker;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeBinding;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.solver.SolverOperation;
import ru.ispras.fortress.solver.function.Function;
import ru.ispras.fortress.solver.function.FunctionTemplate;

/**
 * The SMTTextBuilder class implements logic that generates SMT-LIB code from a syntax structure.
 * Generated code is saved to a text file.
 * 
 * @author Andrei Tatarnikov
 */

final class SMTTextBuilder implements ExprTreeVisitor {
  private final Map<Enum<?>, SolverOperation> operations;
  private final Iterable<Variable> variables;

  private List<StringBuilder> formulas = new LinkedList<StringBuilder>();
  private FunctionDefinitionBuilders functions = new FunctionDefinitionBuilders();

  private StringBuilder currentBuilder = null;
  private int functionCallDepth = 0;

  private final List<DataType> arraysInUse = new ArrayList<DataType>();
  private final Deque<Boolean> castsToBV = new LinkedList<Boolean>();

  /**
   * Creates an instance of a SMT text builder.
   * 
   * @param operations Operation dictionary.
   */

  SMTTextBuilder(Iterable<Variable> variables, Map<Enum<?>, SolverOperation> operations) {
    this.operations = operations;
    this.variables = variables;
  }

  private StringBuilder getCurrentBuilder() {
    assert null != currentBuilder : "The current builder is not assigned.";
    return currentBuilder;
  }

  private void appendToCurrent(String s) {
    assert null != currentBuilder : "The current builder is not assigned.";
    currentBuilder.append(s);
  }

  private void setCurrentBuilder(StringBuilder builder) {
    currentBuilder = builder;
  }

  /**
   * Saves the generated SMT-LIB representation to a text file.
   * 
   * @param fileName The name of the target file.
   * @throws IOException if failed to create the output file.
   */

  public void saveToFile(String fileName, StringBuilder textBuilder) throws IOException {
    class TextWriter {
      private final PrintWriter fileOut;
      private final StringBuilder textOut;

      TextWriter(String fileName, StringBuilder textBuilder) throws IOException {
        final FileWriter file = new FileWriter(fileName);
        this.fileOut = new PrintWriter(file);
        this.textOut = textBuilder;
      }

      public void printf(String format, Object ... args) {
        fileOut.printf(format, args);
        if (null != textOut) {
          textOut.append(String.format(format, args));
        }
      }

      public void println(String x) {
        fileOut.println(x);
        if (null != textOut) {
          textOut.append(x);
          textOut.append("\r\n");
        }
      }

      public void close() {
        fileOut.close();
      }
    }

    TextWriter out = null;
    try {
      out = new TextWriter(fileName, textBuilder);

      int i = 0;
      for (DataType type : arraysInUse) {
        out.printf(DECLARE_CONST, String.format(DEFAULT_ARRAY, i++), textForType(type));
      }

      final StringBuilder variablesListBuilder = new StringBuilder();
      for (Variable variable : variables) {
        // Variables that have values don't need declarations
        // because their values are used in expression as constants.
        if (!variable.hasValue()) {
          out.printf(DECLARE_CONST, variable.getName(), textForType(variable.getData().getType()));

          variablesListBuilder.append(SPACE);
          variablesListBuilder.append(variable.getName());
        }
      }

      for (StringBuilder builder : functions.getBuilders()) {
        out.printf(DEFINE_FUN, builder.toString());
      }

      for (StringBuilder builder : formulas) {
        out.printf(ASSERT, builder.toString());
      }

      out.println(CHECK_SAT);

      if (variablesListBuilder.length() > 0) {
        out.printf(GET_VALUE, variablesListBuilder.toString());
      }

      out.println(GET_MODEL);
      out.println(EXIT);
    } finally {
      if (null != out) {
        out.close();
      }
    }
  }

  private void addFunctionDefinition(Function function) {
    if (functions.isDefined(function.getUniqueName())) {
      return;
    }

    final StringBuilder builder = new StringBuilder();

    builder.append(function.getUniqueName());
    builder.append(SPACE);

    // Forms the parameter list.
    builder.append(BRACKET_OPEN);
    for (int index = 0; index < function.getParameterCount(); ++index) {
      final Variable param = function.getParameter(index);
      builder.append(String.format(PARAM_DEF,
        param.getName(), textForType(param.getData().getType())));
    }
    builder.append(BRACKET_CLOSE);

    // Appends the return type
    builder.append(SPACE);
    builder.append(textForType(function.getReturnType()));

    // Forms the function body
    final StringBuilder previousBuilder = getCurrentBuilder();
    setCurrentBuilder(builder);

    functions.addEntry(function.getUniqueName(), functionCallDepth, builder);

    if (0 == functionCallDepth) {
      functions.beginCallTree();
    }

    functionCallDepth++;

    final ExprTreeWalker walker = new ExprTreeWalker(this);
    walker.visitNode(function.getBody());

    functionCallDepth--;

    if (0 == functionCallDepth) {
      functions.endCallTree();
    }

    setCurrentBuilder(previousBuilder);
  }

  @Override
  public Status getStatus() {
    // We are not going to stop the walker or to skip any subtrees.
    // Therefore, it is always OK.
    return Status.OK;
  }

  @Override
  public void onRootBegin() {
    final StringBuilder builder = new StringBuilder();
    formulas.add(builder);
    setCurrentBuilder(builder);
  }

  @Override
  public void onRootEnd() {
    setCurrentBuilder(null);
  }

  @Override
  public void onOperationBegin(NodeOperation expr) {
    final Enum<?> op = expr.getOperationId();

    if (!operations.containsKey(op)) {
      throw new IllegalArgumentException("Unsupported operation: " + op);
    }

    final SolverOperation operation = operations.get(op);

    final String operationText;
    switch (operation.getKind()) {
      case TEXT:
        operationText = operation.getText();
        break;

      case FUNCTION:
        operationText = operation.getFunction().getUniqueName();
        addFunctionDefinition(operation.getFunction());
        break;

      case TEMPLATE: {
        final DataType[] argTypes = new DataType[expr.getOperandCount()];

        for (int index = 0; index < expr.getOperandCount(); ++index) {
          argTypes[index] = expr.getOperand(index).getDataType();
        }

        final FunctionTemplate template = operation.getTemplate();
        final Function function = template.instantiate(argTypes);

        operationText = function.getUniqueName();
        addFunctionDefinition(function);
        break;
      }

      default: {
        throw new IllegalArgumentException(
          "Unknown operation kind: " + operation.getKind());
      }
    }

    appendToCurrent(SPACE);

    if (expr.getOperandCount() > 0) {
      appendToCurrent(BRACKET_OPEN);
    }

    if (StandardOperation.isParametric(op)) {
      appendToCurrent(BRACKET_OPEN);
      appendToCurrent(UNDERLINE);
      appendToCurrent(SPACE);
    }

    appendToCurrent(operationText);
  }

  @Override
  public void onOperationEnd(NodeOperation expr) {
    if (expr.getOperandCount() > 0) {
      appendToCurrent(BRACKET_CLOSE);
    }
  }

  @Override
  public int[] getOperandOrder() {
    return null;
  }

  @Override
  public void onOperandBegin(NodeOperation expr, Node node, int index) {
    final Enum<?> operationId = expr.getOperationId();
    if (StandardOperation.isFamily(operationId, StandardOperation.Family.BV) &&
        (node.getDataType().getTypeId() == DataTypeId.LOGIC_BOOLEAN)) {

      appendToCurrent(SPACE);
      appendToCurrent(BRACKET_OPEN);

      final SolverOperation ite = operations.get(StandardOperation.ITE);
      appendToCurrent(ite.getText());

      castsToBV.push(true);
    }
    else {
      castsToBV.push(false);
    }
  }

  @Override
  public void onOperandEnd(NodeOperation expr, Node node, int index) {
    if (StandardOperation.isParametric(expr.getOperationId())
        && index == StandardOperation.getParameterCount(expr.getOperationId()) - 1) {
      appendToCurrent(BRACKET_CLOSE);
    }

    final boolean isCastToBVNeeded = castsToBV.pop();
    if (isCastToBVNeeded) {
      onValue(Data.newBitVector(BitVector.TRUE));
      onValue(Data.newBitVector(BitVector.FALSE));
      appendToCurrent(BRACKET_CLOSE);
    }
  }

  @Override
  public void onValue(NodeValue value) {
    onValue(value.getData());
  }

  private void onValue(Data data) {
    appendToCurrent(SPACE);
    if (data.getType().getTypeId() == DataTypeId.MAP) {
      int i = 0;
      final String type = data.getType().toString();

      for (DataType arrayType : arraysInUse) {
        if (arrayType.toString().equals(type)) {
          break;
        }
        ++i;
      }

      if (i >= arraysInUse.size()) {
        arraysInUse.add(data.getType());
      }

      appendToCurrent(String.format(textForData(data), i));
    } else {
      appendToCurrent(textForData(data));
    }
  }

  @Override
  public void onVariable(NodeVariable variable) {
    if (variable.getData().hasValue()) {
      onValue(variable.getData());
    } else {
      appendToCurrent(SPACE);
      appendToCurrent(variable.getName());
    }
  }

  @Override
  public void onBindingBegin(NodeBinding node) {
    appendToCurrent("(let (");
  }

  @Override
  public void onBindingListEnd(NodeBinding node) {
    appendToCurrent(BRACKET_CLOSE);
  }

  @Override
  public void onBindingEnd(NodeBinding node) {
    appendToCurrent(BRACKET_CLOSE);
  }

  @Override
  public void onBoundVariableBegin(NodeBinding node, NodeVariable variable, Node value) {
    appendToCurrent(BRACKET_OPEN);
    appendToCurrent(variable.getName());
    appendToCurrent(SPACE);
  }

  @Override
  public void onBoundVariableEnd(NodeBinding node, NodeVariable variable, Node value) {
    appendToCurrent(BRACKET_CLOSE);
  }
}


final class FunctionDefinitionBuilders {
  private final Set<String> names;
  private final List<StringBuilder> entries;
  private final Map<Integer, List<StringBuilder>> queue;

  private boolean callTreeStarted = false;

  private static final class ReverseComparator implements Comparator<Integer> {
    public int compare(Integer o1, Integer o2) {
      return -o1.compareTo(o2);
    }
  }

  public FunctionDefinitionBuilders() {
    this.names = new HashSet<String>();
    this.entries = new ArrayList<StringBuilder>();
    this.queue = new TreeMap<Integer, List<StringBuilder>>(new ReverseComparator());
  }

  public void beginCallTree() {
    if (callTreeStarted) {
      throw new IllegalStateException("The call tree is already started.");
    }

    callTreeStarted = true;
  }

  public void endCallTree() {
    assert callTreeStarted;

    for (List<StringBuilder> level : queue.values()) {
      for (StringBuilder entry : level) {
        entries.add(entry);
      }
    }

    queue.clear();
    callTreeStarted = false;
  }

  public boolean isDefined(String name) {
    return names.contains(name);
  }

  public void addEntry(String name, Integer depth, StringBuilder entry) {
    if (names.contains(name)) {
      throw new IllegalStateException(String.format(
        "The function %s function is already defined.", name));
    }

    names.add(name);

    final List<StringBuilder> level;
    if (queue.containsKey(depth)) {
      level = queue.get(depth);
    } else {
      level = new ArrayList<StringBuilder>();
      queue.put(depth, level);
    }

    level.add(entry);
  }

  public List<StringBuilder> getBuilders() {
    return Collections.unmodifiableList(entries);
  }
}
