/*
 * Copyright 2011-2018 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.solver.engine.smt;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.DataTypeId;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.ExprTreeVisitor;
import ru.ispras.fortress.expression.ExprTreeWalker;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeBinding;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.solver.SolverOperation;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintUtils;
import ru.ispras.fortress.solver.function.Function;
import ru.ispras.fortress.solver.function.FunctionTemplate;

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

/**
 * The SMTTextBuilder class implements logic that generates SMT-LIB code from a syntax structure.
 * Generated code is saved to a text file.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
final class SmtTextBuilder implements ExprTreeVisitor {
  private final List<String> header;
  private final Map<Enum<?>, SolverOperation> operations;
  private final Iterable<Variable> variables;

  private final List<StringBuilder> formulas = new LinkedList<StringBuilder>();
  private final FunctionDefinitionBuilders functions = new FunctionDefinitionBuilders();

  private StringBuilder currentBuilder = null;
  private int functionCallDepth = 0;

  private final List<DataType> arraysInUse = new ArrayList<DataType>();

  /**
   * Creates an instance of a SMT text builder.
   *
   * @param operations Operation dictionary.
   */
  SmtTextBuilder(
      final List<String> header,
      final Iterable<Variable> variables,
      final Map<Enum<?>, SolverOperation> operations) {
    this.header = new LinkedList<>(header);
    this.operations = operations;
    this.variables = variables;
  }

  private StringBuilder getCurrentBuilder() {
    assert null != currentBuilder : "The current builder is not assigned.";
    return currentBuilder;
  }

  private void appendToCurrent(final String text) {
    assert null != currentBuilder : "The current builder is not assigned.";
    currentBuilder.append(text);
  }

  private void setCurrentBuilder(final StringBuilder builder) {
    currentBuilder = builder;
  }

  public static void saveToFile(
      final String fileName,
      final List<String> header,
      final Collection<? extends Node> formulas,
      final Map<Enum<?>, SolverOperation> operations) throws IOException {

    final Constraint c = ConstraintUtils.newConstraint(formulas);
    final SmtTextBuilder smtBuilder = new SmtTextBuilder(header, c.getVariables(), operations);

    final ExprTreeWalker walker = new ExprTreeWalker(smtBuilder);
    walker.visit(formulas);

    smtBuilder.saveToFile(fileName, new StringBuilder());
  }

  /**
   * Saves the generated SMT-LIB representation to a text file.
   *
   * @param fileName The name of the target file.
   * @param textBuilder Build to put text to be printed in the console.
   * @throws IOException if failed to create the output file.
   */
  public void saveToFile(
      final String fileName,
      final StringBuilder textBuilder) throws IOException {
    class TextWriter {
      private final PrintWriter fileOut;
      private final StringBuilder textOut;

      TextWriter(final String fileName, final StringBuilder textBuilder) throws IOException {
        final FileWriter file = new FileWriter(fileName);
        this.fileOut = new PrintWriter(file);
        this.textOut = textBuilder;
      }

      public void printf(final String format, final Object ... args) {
        fileOut.printf(format, args);
        if (null != textOut) {
          textOut.append(String.format(format, args));
        }
      }

      public void println(final String text) {
        fileOut.println(text);
        if (null != textOut) {
          textOut.append(text);
          textOut.append(System.lineSeparator());
        }
      }

      public void close() {
        fileOut.close();
      }
    }

    TextWriter out = null;
    try {
      out = new TextWriter(fileName, textBuilder);

      for (final String headerLine : header) {
        out.println(headerLine);
      }

      int index = 0;
      for (final DataType type : arraysInUse) {
        out.printf(
            SmtStrings.DECLARE_CONST,
            String.format(SmtStrings.DEFAULT_ARRAY, index++),
            SmtStrings.textForType(type));
      }

      final StringBuilder variablesListBuilder = new StringBuilder();
      for (final Variable variable : variables) {
        // Variables that have values don't need declarations
        // because their values are used in expression as constants.
        if (!variable.hasValue()) {
          out.printf(
              SmtStrings.DECLARE_CONST,
              variable.getName(),
              SmtStrings.textForType(variable.getData().getType()));

          variablesListBuilder.append(System.lineSeparator());
          variablesListBuilder.append("  ");
          variablesListBuilder.append(variable.getName());
        }
      }

      for (final StringBuilder builder : functions.getBuilders()) {
        out.printf(SmtStrings.DEFINE_FUN, builder.toString());
      }

      for (final StringBuilder builder : formulas) {
        out.printf(SmtStrings.ASSERT, builder.toString());
      }

      out.println(SmtStrings.CHECK_SAT);

      if (variablesListBuilder.length() > 0) {
        out.printf(SmtStrings.GET_VALUE, variablesListBuilder.toString());
      }

      out.println(SmtStrings.GET_MODEL);
      out.println(SmtStrings.EXIT);
    } finally {
      if (null != out) {
        out.close();
      }
    }
  }

  private void addFunctionDefinition(final Function function) {
    if (functions.isDefined(function.getUniqueName())) {
      return;
    }

    final StringBuilder builder = new StringBuilder();

    builder.append(function.getUniqueName());
    builder.append(SmtStrings.SPACE);

    // Forms the parameter list.
    builder.append(SmtStrings.BRACKET_OPEN);
    for (int index = 0; index < function.getParameterCount(); ++index) {
      final Variable param = function.getParameter(index);
      builder.append(String.format(SmtStrings.PARAM_DEF,
          param.getName(), SmtStrings.textForType(param.getData().getType())));
    }
    builder.append(SmtStrings.BRACKET_CLOSE);

    // Appends the return type
    builder.append(SmtStrings.SPACE);
    builder.append(SmtStrings.textForType(function.getReturnType()));

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
  public void onBegin() {
    final StringBuilder builder = new StringBuilder();
    formulas.add(builder);
    setCurrentBuilder(builder);
  }

  @Override
  public void onEnd() {
    setCurrentBuilder(null);
  }

  @Override
  public void onOperationBegin(final NodeOperation expr) {
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

    appendToCurrent(SmtStrings.SPACE);

    if (expr.getOperandCount() > 0) {
      appendToCurrent(SmtStrings.BRACKET_OPEN);
    }

    if (StandardOperation.isParametric(op)) {
      appendToCurrent(SmtStrings.BRACKET_OPEN);
      appendToCurrent(SmtStrings.UNDERLINE);
      appendToCurrent(SmtStrings.SPACE);
    }

    appendToCurrent(operationText);
  }

  @Override
  public void onOperationEnd(final NodeOperation expr) {
    if (expr.getOperandCount() > 0) {
      appendToCurrent(SmtStrings.BRACKET_CLOSE);
    }
  }

  @Override
  public int[] getOperandOrder() {
    return null;
  }

  @Override
  public void onOperandBegin(
      final NodeOperation expr,
      final Node node,
      final int index) {
  }

  @Override
  public void onOperandEnd(
      final NodeOperation expr,
      final Node node,
      final int index) {
    if (StandardOperation.isParametric(expr.getOperationId())
        && index == StandardOperation.getParameterCount(expr.getOperationId()) - 1) {
      appendToCurrent(SmtStrings.BRACKET_CLOSE);
    }
  }

  @Override
  public void onValue(final NodeValue value) {
    onValue(value.getData());
  }

  private void onValue(final Data data) {
    appendToCurrent(SmtStrings.SPACE);
    if (data.isType(DataTypeId.MAP)) {
      int index = 0;
      final String type = data.getType().toString();

      for (final DataType arrayType : arraysInUse) {
        if (arrayType.toString().equals(type)) {
          break;
        }
        ++index;
      }

      if (index >= arraysInUse.size()) {
        arraysInUse.add(data.getType());
      }

      appendToCurrent(String.format(SmtStrings.textForData(data), index));
    } else {
      appendToCurrent(SmtStrings.textForData(data));
    }
  }

  @Override
  public void onVariable(final NodeVariable variable) {
    if (variable.getData().hasValue()) {
      onValue(variable.getData());
    } else {
      appendToCurrent(SmtStrings.SPACE);
      appendToCurrent(variable.getName());
    }
  }

  @Override
  public void onBindingBegin(final NodeBinding node) {
    appendToCurrent("(let (");
  }

  @Override
  public void onBindingListEnd(final NodeBinding node) {
    appendToCurrent(SmtStrings.BRACKET_CLOSE);
  }

  @Override
  public void onBindingEnd(final NodeBinding node) {
    appendToCurrent(SmtStrings.BRACKET_CLOSE);
  }

  @Override
  public void onBoundVariableBegin(
      final NodeBinding node,
      final NodeVariable variable,
      final Node value) {
    appendToCurrent(SmtStrings.BRACKET_OPEN);
    appendToCurrent(variable.getName());
    appendToCurrent(SmtStrings.SPACE);
  }

  @Override
  public void onBoundVariableEnd(
      final NodeBinding node,
      final NodeVariable variable,
      final Node value) {
    appendToCurrent(SmtStrings.BRACKET_CLOSE);
  }

  private static final class FunctionDefinitionBuilders {
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
      this.names = new HashSet<>();
      this.entries = new ArrayList<>();
      this.queue = new TreeMap<>(new ReverseComparator());
    }

    public void beginCallTree() {
      if (callTreeStarted) {
        throw new IllegalStateException("The call tree is already started.");
      }

      callTreeStarted = true;
    }

    public void endCallTree() {
      assert callTreeStarted;

      for (final List<StringBuilder> level : queue.values()) {
        for (final StringBuilder entry : level) {
          entries.add(entry);
        }
      }

      queue.clear();
      callTreeStarted = false;
    }

    public boolean isDefined(final String name) {
      return names.contains(name);
    }

    public void addEntry(
        final String name,
        final Integer depth,
        final StringBuilder entry) {
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
}


