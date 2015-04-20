/*
 * Copyright 2011-2015 ISP RAS (http://www.ispras.ru)
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

import static ru.ispras.fortress.util.InvariantChecks.checkNotNull;

import java.io.File;
import java.io.IOException;
import java.io.Reader;
import java.util.ArrayList;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.Map;
import java.util.regex.Pattern;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.DataTypeId;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.data.types.datamap.DataMap;
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
import ru.ispras.fortress.util.Pair;

/**
 * The SmtTextSolver class implements logic of a constraint solver that uses the Z3 tool by Microsoft
 * Research. The constraint is translated to STM-LIB code that is then saved to a file and processed
 * to the tool.
 * 
 * @author Andrei Tatarnikov
 */

public abstract class SmtTextSolver extends SolverBase {
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

  public SmtTextSolver(String name, String desc) {
    super(name, desc, EnumSet.of(ConstraintKind.FORMULA_BASED), true);
    initStandardOperations();
  }

  protected abstract Reader invokeSolver(String path) throws IOException;
  protected abstract String getSolverPath();

  private static void solverFileExistsCheck(String solverPath) {
    if (null == solverPath) {
      throw new IllegalStateException(String.format(NO_SOLVER_PATH_ERR_FRMT, "null"));
    }

    if (solverPath.isEmpty()) {
      throw new IllegalStateException(String.format(NO_SOLVER_PATH_ERR_FRMT, "empty string"));
    }

    if (!new File(solverPath).isFile()) {
      throw new IllegalStateException(String.format(NO_SOLVER_FILE_ERR_FRMT, solverPath));
    }
  }

  @Override
  public SolverResult solve(Constraint constraint) {
    checkNotNull(constraint, "constraint");

    supportedKindCheck(constraint.getKind());
    solverFileExistsCheck(getSolverPath());

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

      final Reader reader = invokeSolver(tempFilePath);
      boolean isStatusSet = false;

      final Context context =
          new Context(variablesMap(constraint.getUnknownVariables()));

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
          parseModel(resultBuilder, e, context);
        } else if (!e.isNil() && e.isList()) {
          parseVariables(resultBuilder, e, context);
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

  private static final class Context {
    public final Map<String, Variable> required;
    public final Map<String, Variable> deferred;

    public final Map<String, ESExpr> model;
    public final Map<String, Data> parsed;

    public final ESExprMatcher CAST_ARRAY =
        new ESExprMatcher("(_ as-array %a)");

    public final ESExprMatcher CONST_ARRAY_Z3 =
        new ESExprMatcher("((as const (Array %s %s)) %s)");

    public final ESExprMatcher CONST_ARRAY_CVC4 =
        new ESExprMatcher("(__array_store_all__ (Array %s %s) %s)");

    public final ESExprMatcher STORE = new ESExprMatcher("(store %s %s %s)");
    public final ESExprMatcher MINUS = new ESExprMatcher("(- %a)");
    public final ESExprMatcher CAST = new ESExprMatcher("(_ %a %a)");
    public final ESExprMatcher ITE = new ESExprMatcher("(ite (= %a %s) %s %s)");

    public Context(Map<String, Variable> required) {
      this.required = required;
      this.deferred = new HashMap<>();
      this.model = new HashMap<>();
      this.parsed = new HashMap<>();
    }
  }

  private static void parseVariables(SolverResultBuilder builder,
                                     ESExpr results,
                                     Context ctx) {
    for (ESExpr e : results.getListItems()) {
      final ESExpr value = e.getItems().get(1);
      final String reqName = getLiteral(e, 0);

      if (ctx.CAST_ARRAY.matches(value)) {
        ctx.deferred.put(getLiteral(value, 2),
                         ctx.required.get(getLiteral(e, 0)));
      } else {
        final Variable image = ctx.required.remove(reqName);
        final Data data = parseValueExpr(value, image.getType(), ctx);
        builder.addVariable(new Variable(image.getName(), data));
      }
    }
  }

  private static Data parseValueExpr(ESExpr e, DataType type, Context ctx) {
    switch (type.getTypeId()) {
    case BIT_VECTOR:
      if (ctx.CAST.matches(e)) {
        return parseAtom(getLiteral(e, 1), type);
      }
      return parseAtom(e.getLiteral(), type);

    case MAP:
      return parseArray(e, type, ctx);
    }
    if (ctx.MINUS.matches(e)) {
      return parseAtom("-" + getLiteral(e, 1), type);
    }
    return parseAtom(e.getLiteral(), type);
  }

  private static Data parseArray(ESExpr e, DataType type, Context ctx) {
    if (ctx.CAST_ARRAY.matches(e)) {
      return valueReference(getLiteral(e, 2), type, ctx);
    }

    if (e.isAtom() && ctx.model.containsKey(e.getLiteral())) {
        return valueReference(e.getLiteral(), type, ctx);
    }

    final DataType keyType =
        (DataType) type.getAttribute(DataTypeId.Attribute.KEY);
    final DataType valueType =
        (DataType) type.getAttribute(DataTypeId.Attribute.VALUE);

    if (ctx.CONST_ARRAY_Z3.matches(e)) {
      final Data constant = parseValueExpr(e.getItems().get(1), valueType, ctx);
      return Data.newArray(constantArray(keyType, constant));
    }

    if (ctx.CONST_ARRAY_CVC4.matches(e)) {
      final Data constant = parseValueExpr(e.getItems().get(2), valueType, ctx);
      return Data.newArray(constantArray(keyType, constant));
    }

    if (ctx.ITE.matches(e)) {
      return Data.newArray(parseIteArray(e, type, ctx));
    }

    if (ctx.STORE.matches(e)) {
      return Data.newArray(parseStoreArray(e, type, ctx));
    }

    final Data constant = parseValueExpr(e, valueType, ctx);
    return Data.newArray(constantArray(keyType, constant));
  }

  private static DataMap parseIteArray(ESExpr e, DataType type, Context ctx) {
    final DataType keyType =
        (DataType) type.getAttribute(DataTypeId.Attribute.KEY);
    final DataType valueType =
        (DataType) type.getAttribute(DataTypeId.Attribute.VALUE);

    final DataMap map = new DataMap(keyType, valueType);
    while (ctx.ITE.matches(e)) {
      final ESExpr key = e.getItems().get(1).getItems().get(2);
      final ESExpr value = e.getItems().get(2);

      map.put(parseValueExpr(key, keyType, ctx),
              parseValueExpr(value, valueType, ctx));

      e = e.getItems().get(3);
    }
    map.setConstant(parseValueExpr(e, valueType, ctx));

    return map;
  }

  private static DataMap parseStoreArray(ESExpr e, DataType type, Context ctx) {
    final DataType keyType =
        (DataType) type.getAttribute(DataTypeId.Attribute.KEY);
    final DataType valueType =
        (DataType) type.getAttribute(DataTypeId.Attribute.VALUE);

    final ArrayList<Pair<Data, Data>> pairs = new ArrayList<>();
    while (ctx.STORE.matches(e)) {
      final ESExpr key = e.getItems().get(2);
      final ESExpr value = e.getItems().get(3);

      pairs.add(new Pair<>(parseValueExpr(key, keyType, ctx),
                         parseValueExpr(value, valueType, ctx)));

      e = e.getItems().get(1);
    }
    final DataMap map = ((DataMap) parseArray(e, type, ctx).getValue()).copy();
    for (Pair<Data, Data> pair : pairs) {
      map.put(pair.first, pair.second);
    }
    return map;
  }

  private static Data valueReference(String name, DataType type, Context ctx) {
    final Data cached = ctx.parsed.get(name);
    if (cached == null) {
      final Data data = parseValueExpr(ctx.model.get(name), type, ctx);
      ctx.parsed.put(name, data);
      return data;
    }
    return cached;
  }

  private static DataMap constantArray(DataType keyType, Data value) {
    final DataMap map = new DataMap(keyType, value.getType());
    map.setConstant(value);

    return map;
  }

  private static Data parseAtom(String atom, DataType type) {
    final int radix;
    if (Pattern.compile(SMTRegExp.LINE_START + SMTRegExp.VALUE_BIN).matcher(atom).matches()) {
      radix = 2;
    } else if (Pattern.compile(SMTRegExp.LINE_START + SMTRegExp.VALUE_HEX).matcher(atom).matches()) {
      radix = 16;
    } else {
      radix = 10; // decimal value by default
    }
    return type.valueOf(atom.replaceAll(SMTRegExp.VALUE_TRIM_PTRN, ""), radix);
  }

  private static void parseModel(SolverResultBuilder builder,
                                 ESExpr model,
                                 Context ctx) {
    final ESExprMatcher define = new ESExprMatcher("(define-fun %a %s %s %s)");
    for (final ESExpr e : model.getListItems()) {
      if (!define.matches(e)) {
        continue;
      }
      ctx.model.put(getLiteral(e, 1), e.getItems().get(4));
    }

    for (final Map.Entry<String, Variable> entry : ctx.deferred.entrySet()) {
      final Variable var = entry.getValue();
      final Data data =
          parseArray(ctx.model.get(var.getName()), var.getType(), ctx);
      builder.addVariable(new Variable(var.getName(), data));
    }
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
    addStandardOperation(StandardOperation.BVUDIV, "bvudiv");
    addStandardOperation(StandardOperation.BVSDIV, "bvsdiv");
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

    for (final StandardFunction template : StandardFunction.values()) {
      addCustomOperation(template);
    }
  }
}
