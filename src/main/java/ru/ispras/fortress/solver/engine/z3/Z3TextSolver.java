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

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.Map;
import java.util.regex.Pattern;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.esexpr.ESExpr;
import ru.ispras.fortress.esexpr.ESExprMatcher;
import ru.ispras.fortress.esexpr.ESExprParser;
import ru.ispras.fortress.expression.ExprTreeWalker;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.solver.Environment;
import ru.ispras.fortress.solver.SolverBase;
import ru.ispras.fortress.solver.SolverResult;
import ru.ispras.fortress.solver.SolverResultBuilder;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintKind;
import ru.ispras.fortress.solver.constraint.Formulas;
import ru.ispras.fortress.solver.function.StandardFunction;

/**
 * The Z3TextSolver class implements logic of a constraint solver that uses the Z3 tool by Microsoft
 * Research. The constraint is translated to STM-LIB code that is then saved to a file and processed
 * to the tool.
 * 
 * @author Andrei Tatarnikov
 */

public final class Z3TextSolver extends SolverBase {
  private static final String NAME = "Z3 (text-based interface)";

  private static final String DESCRIPTION =
    "Solves constraints using the Z3 solver. " + 
    "Interacts with the solver via text files and command line.";

  private static final String TEMP_FILE = "ispras_z3_temp";
  private static final String TEMP_FILE_SUFFIX = ".smt2";

  private static final String UNK_OUTPUT_ERR_FRMT =
    "Unexpected solver output: \"%s\"";

  private static final String NO_SOLVER_PATH_ERR_FRMT =
    "The path to the external constraint solver executable " + "is not assigned (equals %s).";

  private static final String NO_SOLVER_FILE_ERR_FRMT =
    "The external constraint solver executable (%s) does not exist or " +
    "the path is not a valid file path.";

  private static final String IO_EXCEPTION_ERR =
    "I/O exception in the process of a solving the constraint. Details: ";

  public Z3TextSolver() {
    super(NAME, DESCRIPTION, EnumSet.of(ConstraintKind.FORMULA_BASED), true);
    initStandardOperations();
  }

  private static void solverFileExistsCheck(String solverPath) {
    if (null == solverPath) {
      throw new NullPointerException(String.format(NO_SOLVER_PATH_ERR_FRMT, "null"));
    }

    if (solverPath.isEmpty()) {
      throw new NullPointerException(String.format(NO_SOLVER_PATH_ERR_FRMT, "empty string"));
    }

    if (!new File(solverPath).isFile()) {
      throw new IllegalStateException(String.format(NO_SOLVER_FILE_ERR_FRMT, solverPath));
    }
  }

  @Override
  public SolverResult solve(Constraint constraint) {
    notNullCheck(constraint, "constraint");

    supportedKindCheck(constraint.getKind());
    solverFileExistsCheck(Environment.getSolverPath());
    
    final StringBuilder textBuilder = new StringBuilder();
    final SolverResultBuilder resultBuilder = new SolverResultBuilder(SolverResult.Status.ERROR);

    final SMTTextBuilder smtTextBuilder =
      new SMTTextBuilder(constraint.getVariables(), getOperations());

    final ExprTreeWalker walker = new ExprTreeWalker(smtTextBuilder);

    File tempFile = null;
    try {
      walker.visit(((Formulas) constraint.getInnerRep()).exprs());
      tempFile = File.createTempFile(TEMP_FILE, TEMP_FILE_SUFFIX);

      final String tempFilePath = tempFile.getPath();
      smtTextBuilder.saveToFile(tempFilePath, textBuilder);

      final Process process = runSolver(Environment.getSolverPath(), tempFilePath, "");

      final BufferedReader reader = 
        new BufferedReader(new InputStreamReader(process.getInputStream()));

      boolean isStatusSet = false;

      final Map<String, Variable> required =
          variablesMap(constraint.getUnknownVariables());

      final Map<String, Variable> deferred = new HashMap<>();

      final ESExprParser parser = new ESExprParser(reader);
      ESExpr e = parser.next();
      while (e != null) {
        if (isStatus(e)) {
          if (!isStatusSet) { 
            setStatus(resultBuilder, e.getLiteral());
            isStatusSet = true;
          }
        } else if (isError(e)) {
          resultBuilder.addError(getLiteral(e, 1));
          if (!isStatusSet) {
            resultBuilder.setStatus(SolverResult.Status.ERROR);
            isStatusSet = true;
          }
        } else if (isModel(e)) {
          parseModel(resultBuilder, e, deferred);
        } else if (!e.isNil() && e.isList()) {
          parseVariables(resultBuilder, e, required, deferred);
        } else {
          assert false : String.format(UNK_OUTPUT_ERR_FRMT, e.toString());
          resultBuilder.addError(String.format(UNK_OUTPUT_ERR_FRMT, e.toString()));
        }
        e = parser.next();
      }
    } catch (IOException e) {
      resultBuilder.setStatus(SolverResult.Status.ERROR);
      resultBuilder.addError(IO_EXCEPTION_ERR + e.getMessage());
    } finally {
      if (null != tempFile && !Environment.isDebugMode()) {
        tempFile.delete();
      }
    }

    if (resultBuilder.hasErrors()) {
      resultBuilder.addError(textBuilder.toString());
    }

    return resultBuilder.build();
  }

  private static Map<String, Variable> variablesMap(Iterable<Variable> vars) {
    final Map<String, Variable> map = new HashMap<>();
    for (Variable var : vars) {
      map.put(var.getName(), var);
    }
    return map;
  }

  private static boolean isStatus(ESExpr e) {
    if (!e.isAtom()) {
      return false;
    }
    final String literal = e.getLiteral();
    return literal.equals(SMTRegExp.SAT) ||
           literal.equals(SMTRegExp.UNSAT) ||
           literal.equals(SMTRegExp.UNKNOWN);
  }

  private static void setStatus(SolverResultBuilder builder, String statusStr) {
    final SolverResult.Status status;
    switch (statusStr) {
      case SMTRegExp.SAT:
        status = SolverResult.Status.SAT;
        break;

      case SMTRegExp.UNSAT:
        status = SolverResult.Status.UNSAT;
        break;

      default:
        status = SolverResult.Status.UNKNOWN;
    }
    builder.setStatus(status);
  }

  private static boolean isError(ESExpr e) {
    final ESExprMatcher matcher = new ESExprMatcher("(error %a)");
    return matcher.matches(e);
  }

  private static String getLiteral(ESExpr e, int n) {
    return e.getItems().get(n).getLiteral();
  }

  private static boolean isModel(ESExpr e) {
    return e.isList() &&
           !e.isNil() &&
           getLiteral(e, 0).equals("model");
  }

  private Process runSolver(String solverPath, String constraintFileName, String solverArgs)
      throws IOException {
    final ProcessBuilder pb = new ProcessBuilder(solverPath, constraintFileName, solverArgs);
    return pb.start();
  }

  private static void parseVariables(SolverResultBuilder builder,
                                     ESExpr results,
                                     Map<String, Variable> required,
                                     Map<String, Variable> deferred) {
    final ESExprMatcher asArray =
        new ESExprMatcher("(_ as-array %a)");
    final ESExprMatcher constArray =
        new ESExprMatcher("((as const (Array %s %s)) %s)");
    final ESExprMatcher minus = new ESExprMatcher("(- %a)");

    for (ESExpr e : results.getListItems()) {
      final ESExpr value = e.getItems().get(1);
      final String reqName = getLiteral(e, 0);

      if (value.isAtom() || minus.matches(value)) {
        final Variable var = required.remove(reqName);
        String val = value.getLiteral();
        if (!value.isAtom()) {
          val = getLiteral(value, 0) + getLiteral(value, 1);
        }
        builder.addVariable(parseVariable(var.getName(), var.getType(), val));
      } else if (asArray.matches(value)) {
        deferred.put(getLiteral(value, 2), required.get(getLiteral(e, 0)));
      } else if (constArray.matches(value)) {
        // FIXME What are const arrays in Fortress?
        final Variable var = required.remove(reqName);
        builder.addVariable(new Variable(var.getName(), var.getType().valueOf("()", 10)));
      }
    }
  }

  private static Variable parseVariable(String name, DataType typeInfo, String valueText) {
    final int radix;

    if (Pattern.compile(SMTRegExp.LINE_START + SMTRegExp.VALUE_BIN).matcher(valueText).matches()) {
      radix = 2;
    } else if (Pattern.compile(SMTRegExp.LINE_START + SMTRegExp.VALUE_HEX).matcher(valueText).matches()) {
      radix = 16;
    } else {
      radix = 10; // decimal value by default
    }

    final Data data = typeInfo.valueOf(valueText.replaceAll(SMTRegExp.VALUE_TRIM_PTRN, ""), radix);
    return new Variable(name, data);
  }

  private static void parseModel(SolverResultBuilder builder,
                                 ESExpr model,
                                 Map<String, Variable> deferred) {
    final ESExprMatcher define = new ESExprMatcher("(define-fun %a %s %s %s)");

    final Map<String, ESExpr> values = new HashMap<>(model.getItems().size());
    for (ESExpr e : model.getListItems()) {
      if (!define.matches(e)) {
        continue;
      }
      values.put(getLiteral(e, 1), e.getItems().get(4));
    }
    final Map<String, String> cache = new HashMap<>();
    for (Map.Entry<String, Variable> entry : deferred.entrySet()) {
      final String array = arrayModelToText(entry.getKey(), values, cache);
      final Variable origin = entry.getValue();
      builder.addVariable(new Variable(origin.getName(), origin.getType().valueOf(array, 10)));
    }
  }

  private static String arrayModelToText(String name,
                                         Map<String, ESExpr> model,
                                         Map<String, String> cache) {
    if (cache.containsKey(name)) {
      return cache.get(name);
    }
    final ESExprMatcher ite = new ESExprMatcher("(ite (= %a %s) %s %s)");
    final ESExprMatcher asArray = new ESExprMatcher("(_ as-array %a)");
    final ESExprMatcher minus = new ESExprMatcher("(- %a)");

    ESExpr e = model.get(name);
    if (asArray.matches(e)) {
      final String value = arrayModelToText(getLiteral(e, 2), model, cache);
      cache.put(name, value);
      return value;
    }

    final StringBuilder builder = new StringBuilder();
    builder.append('(');

    while (ite.matches(e)) {
      final ESExpr esKey = e.getItems().get(1).getItems().get(2);
      final ESExpr esValue = e.getItems().get(2);

      String key = esKey.getLiteral();
      if (asArray.matches(esKey)) {
        key = arrayModelToText(getLiteral(esKey, 2), model, cache);
      } else if (minus.matches(esKey)) {
        key = getLiteral(esKey, 0) + getLiteral(esKey, 1);
      }
      String value = esValue.getLiteral();
      if (asArray.matches(esValue)) {
        value = arrayModelToText(getLiteral(esValue, 2), model, cache);
      } else if (minus.matches(esValue)) {
        value = getLiteral(esValue, 0) + getLiteral(esValue, 1);
      }
      builder.append('(').append(key).append(':').append(value).append(')');

      e = e.getItems().get(3);
    }
    builder.append(')');

    final String array = builder.toString();
    cache.put(name, array);
    return array;
  }

  private void initStandardOperations() {
    /* Logic Operations */
    addStandardOperation(StandardOperation.EQ, "=");
    addStandardOperation(StandardOperation.NOTEQ, "distinct");
    addStandardOperation(StandardOperation.EQCASE, "=");
    addStandardOperation(StandardOperation.NOTEQCASE, "distinct");
    addStandardOperation(StandardOperation.AND, "and");
    addStandardOperation(StandardOperation.OR, "or");
    addStandardOperation(StandardOperation.NOT, "not");
    addStandardOperation(StandardOperation.XOR, "xor");
    addStandardOperation(StandardOperation.IMPL, "=>");
    addStandardOperation(StandardOperation.ITE, "ite");

    // Logic arithmetic
    addStandardOperation(StandardOperation.MINUS, "-");
    addStandardOperation(StandardOperation.PLUS, "+");
    addStandardOperation(StandardOperation.ADD, "+");
    addStandardOperation(StandardOperation.SUB, "-");
    addStandardOperation(StandardOperation.MUL, "*");
    addStandardOperation(StandardOperation.DIV, "div");
    addStandardOperation(StandardOperation.REM, "rem");
    addStandardOperation(StandardOperation.MOD, "mod");
    addStandardOperation(StandardOperation.GREATER, ">");
    addStandardOperation(StandardOperation.GREATEREQ, ">=");
    addStandardOperation(StandardOperation.LESS, "<");
    addStandardOperation(StandardOperation.LESSEQ, "<=");
    addStandardOperation(StandardOperation.POWER, "^");

    /* Bitvector operations */

    // Basic Bitvector Arithmetic
    addStandardOperation(StandardOperation.BVADD, "bvadd");
    addStandardOperation(StandardOperation.BVSUB, "bvsub");
    addStandardOperation(StandardOperation.BVNEG, "bvneg");
    addStandardOperation(StandardOperation.BVMUL, "bvmul");
    addStandardOperation(StandardOperation.BVUREM, "bvurem");
    addStandardOperation(StandardOperation.BVSREM, "bvsrem");
    addStandardOperation(StandardOperation.BVSMOD, "bvsmod");
    addStandardOperation(StandardOperation.BVLSHL, "bvshl");
    addStandardOperation(StandardOperation.BVASHL, "bvshl");
    addStandardOperation(StandardOperation.BVLSHR, "bvlshr");
    addStandardOperation(StandardOperation.BVASHR, "bvashr");
    addStandardOperation(StandardOperation.BVCONCAT, "concat");
    addStandardOperation(StandardOperation.BVREPEAT, "repeat");
    addStandardOperation(StandardOperation.BVROL, "rotate_left");
    addStandardOperation(StandardOperation.BVROR, "rotate_right");
    addStandardOperation(StandardOperation.BVZEROEXT, "zero_extend");
    addStandardOperation(StandardOperation.BVSIGNEXT, "sign_extend");

    // Bitwise Operations
    addStandardOperation(StandardOperation.BVOR, "bvor");
    addStandardOperation(StandardOperation.BVXOR, "bvxor");
    addStandardOperation(StandardOperation.BVAND, "bvand");
    addStandardOperation(StandardOperation.BVNOT, "bvnot");
    addStandardOperation(StandardOperation.BVNAND, "bvnand");
    addStandardOperation(StandardOperation.BVNOR, "bvnor");
    addStandardOperation(StandardOperation.BVXNOR, "bvxnor");

    // Predicates over Bitvectors
    addStandardOperation(StandardOperation.BVULE, "bvule");
    addStandardOperation(StandardOperation.BVULT, "bvult");
    addStandardOperation(StandardOperation.BVUGE, "bvuge");
    addStandardOperation(StandardOperation.BVUGT, "bvugt");
    addStandardOperation(StandardOperation.BVSLE, "bvsle");
    addStandardOperation(StandardOperation.BVSLT, "bvslt");
    addStandardOperation(StandardOperation.BVSGE, "bvsge");
    addStandardOperation(StandardOperation.BVSGT, "bvsgt");

    addStandardOperation(StandardOperation.BVEXTRACT, "extract");

    /* Array operations */
    addStandardOperation(StandardOperation.SELECT, "select");
    addStandardOperation(StandardOperation.STORE, "store");

    for (StandardFunction template : StandardFunction.values()) {
      addCustomOperation(template);
    }
  }
}
