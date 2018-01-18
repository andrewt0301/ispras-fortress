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
import ru.ispras.fortress.data.types.bitvector.BitVector;
import ru.ispras.fortress.data.types.datamap.DataMap;
import ru.ispras.fortress.esexpr.ESExpr;
import ru.ispras.fortress.esexpr.ESExprMatcher;
import ru.ispras.fortress.esexpr.ESExprParser;
import ru.ispras.fortress.expression.ExprTreeWalker;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.Nodes;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.solver.Environment;
import ru.ispras.fortress.solver.SolverBase;
import ru.ispras.fortress.solver.SolverResult;
import ru.ispras.fortress.solver.SolverResultBuilder;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintKind;
import ru.ispras.fortress.solver.constraint.Formulas;
import ru.ispras.fortress.solver.function.Function;
import ru.ispras.fortress.solver.function.StandardFunction;
import ru.ispras.fortress.util.InvariantChecks;
import ru.ispras.fortress.util.Pair;

import java.io.File;
import java.io.IOException;
import java.io.Reader;
import java.util.ArrayList;
import java.util.Collection;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Pattern;

/**
 * The {@link SmtTextSolver} class implements logic of a constraint solver that uses external
 * SMT solvers. The constraint is translated to STM-LIB code that is then saved to a file and
 * processed by the external solver.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public abstract class SmtTextSolver extends SolverBase {
  private static final String TEMP_FILE = "ispras_z3_temp";
  private static final String TEMP_FILE_SUFFIX = ".smt2";

  private static final String UNK_OUTPUT_ERR_FRMT =
      "%s: Unexpected solver output: \"%s\"";

  private static final String NO_SOLVER_PATH_ERR_FRMT =
      "%s: The path to the external constraint solver executable is not assigned (equals %s).";

  private static final String NO_SOLVER_FILE_ERR_FRMT =
      "%s: The external constraint solver executable (%s) does not exist or "
          + "the path is not a valid file path.";

  private static final String IO_EXCEPTION_ERR =
      "%s: I/O exception in the process of a solving the constraint. Details: %s";

  public SmtTextSolver(
      final String name,
      final String desc,
      final String envVarName) {
    super(name, desc, EnumSet.of(ConstraintKind.FORMULA_BASED), true, envVarName);
    initStandardOperations();
  }

  /**
   * Returns the list of solver-specific header lines.
   * @return The list of solver-specific header lines.
   */
  protected abstract List<String> getHeader();

  protected abstract Reader invokeSolver(String path) throws IOException;

  private void solverFileExistsCheck(final String solverPath) {
    if (null == solverPath) {
      throw new IllegalStateException(String.format(
          NO_SOLVER_PATH_ERR_FRMT, getName(), "null"));
    }

    if (solverPath.isEmpty()) {
      throw new IllegalStateException(String.format(
          NO_SOLVER_PATH_ERR_FRMT, getName(), "empty string"));
    }

    if (!new File(solverPath).isFile()) {
      throw new IllegalStateException(String.format(
          NO_SOLVER_FILE_ERR_FRMT, getName(), solverPath));
    }
  }

  @Override
  public SolverResult solve(final Constraint constraint) {
    InvariantChecks.checkNotNull(constraint);

    supportedKindCheck(constraint.getKind());
    solverFileExistsCheck(getSolverPath());

    final StringBuilder textBuilder = new StringBuilder();
    final SolverResultBuilder resultBuilder = new SolverResultBuilder(SolverResult.Status.ERROR);

    final SmtTextBuilder smtTextBuilder =
        new SmtTextBuilder(getHeader(), constraint.getVariables(), getOperations());

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
      ESExpr expr = parser.next();
      while (expr != null) {
        if (isStatus(expr)) {
          if (!isStatusSet) {
            setStatus(resultBuilder, expr.getLiteral());
            isStatusSet = true;
          }
        } else if (isError(expr)) {
          resultBuilder.addError(getLiteral(expr, 1));
          if (!isStatusSet) {
            resultBuilder.setStatus(SolverResult.Status.ERROR);
            isStatusSet = true;
          }
        } else if (isModel(expr)) {
          parseModel(resultBuilder, expr, context);
        } else if (!expr.isNil() && expr.isList()) {
          parseVariables(resultBuilder, expr, context);
        } else {
          assert false : String.format(UNK_OUTPUT_ERR_FRMT, getName(), expr.toString());
          resultBuilder.addError(String.format(UNK_OUTPUT_ERR_FRMT, getName(), expr.toString()));
        }
        expr = parser.next();
      }
    } catch (IOException e) {
      resultBuilder.setStatus(SolverResult.Status.ERROR);
      resultBuilder.addError(String.format(IO_EXCEPTION_ERR, getName(), e.getMessage()));
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

  private static Map<String, Variable> variablesMap(final Iterable<Variable> vars) {
    final Map<String, Variable> map = new HashMap<>();
    for (final Variable var : vars) {
      map.put(var.getName(), var);
    }
    return map;
  }

  private static boolean isStatus(final ESExpr e) {
    if (!e.isAtom()) {
      return false;
    }
    final String literal = e.getLiteral();
    return literal.equals(SmtRegExp.SAT)
        || literal.equals(SmtRegExp.UNSAT)
        || literal.equals(SmtRegExp.UNKNOWN);
  }

  private static void setStatus(
      final SolverResultBuilder builder,
      final String statusStr) {
    final SolverResult.Status status;
    switch (statusStr) {
      case SmtRegExp.SAT:
        status = SolverResult.Status.SAT;
        break;

      case SmtRegExp.UNSAT:
        status = SolverResult.Status.UNSAT;
        break;

      default:
        status = SolverResult.Status.UNKNOWN;
    }
    builder.setStatus(status);
  }

  private static boolean isError(final ESExpr e) {
    final ESExprMatcher matcher = new ESExprMatcher("(error %a)");
    return matcher.matches(e);
  }

  private static String getLiteral(final ESExpr e, final int n) {
    return e.getItems().get(n).getLiteral();
  }

  private static boolean isModel(final ESExpr e) {
    return e.isList()
        && !e.isNil()
        && getLiteral(e, 0).equals("model");
  }

  private static final class Context {
    public final Map<String, Variable> required;
    public final Map<String, Variable> deferred;

    public final Map<String, ESExpr> model;
    public final Map<String, Data> parsed;

    public static final ESExprMatcher CAST_ARRAY =
        new ESExprMatcher("(_ as-array %a)");

    public static final ESExprMatcher CONST_ARRAY_Z3 =
        new ESExprMatcher("((as const (Array %s %s)) %s)");

    public static final ESExprMatcher CONST_ARRAY_CVC4 =
        new ESExprMatcher("(__array_store_all__ (Array %s %s) %s)");

    public static final ESExprMatcher STORE = new ESExprMatcher("(store %s %s %s)");
    public static final ESExprMatcher MINUS = new ESExprMatcher("(- %a)");
    public static final ESExprMatcher CAST = new ESExprMatcher("(_ %a %a)");
    public static final ESExprMatcher ITE = new ESExprMatcher("(ite (= %a %s) %s %s)");

    public Context(final Map<String, Variable> required) {
      this.required = required;
      this.deferred = new HashMap<>();
      this.model = new HashMap<>();
      this.parsed = new HashMap<>();
    }
  }

  private static void parseVariables(
      final SolverResultBuilder builder,
      final ESExpr results,
      final Context ctx) {
    for (final ESExpr e : results.getListItems()) {
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

  private static Data parseValueExpr(
      final ESExpr e,
      final DataType type,
      final Context ctx) {
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

  private static Data parseArray(
      final ESExpr e,
      final DataType type,
      final Context ctx) {
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

  private static DataMap parseIteArray(
      ESExpr e,
      final DataType type,
      final Context ctx) {
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

  private static DataMap parseStoreArray(
      ESExpr e,
      final DataType type,
      final Context ctx) {
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
    for (final Pair<Data, Data> pair : pairs) {
      map.put(pair.first, pair.second);
    }
    return map;
  }

  private static Data valueReference(
      final String name,
      final DataType type,
      final Context ctx) {
    final Data cached = ctx.parsed.get(name);
    if (cached == null) {
      final Data data = parseValueExpr(ctx.model.get(name), type, ctx);
      ctx.parsed.put(name, data);
      return data;
    }
    return cached;
  }

  private static DataMap constantArray(final DataType keyType, final Data value) {
    final DataMap map = new DataMap(keyType, value.getType());
    map.setConstant(value);

    return map;
  }

  private static Data parseAtom(final String atom, final DataType type) {
    final int radix;
    if (Pattern.compile(SmtRegExp.LINE_START + SmtRegExp.VALUE_BIN).matcher(atom).matches()) {
      radix = 2;
    } else if (Pattern.compile(SmtRegExp.LINE_START
        + SmtRegExp.VALUE_HEX).matcher(atom).matches()) {
      radix = 16;
    } else {
      radix = 10; // decimal value by default
    }
    return type.valueOf(atom.replaceAll(SmtRegExp.VALUE_TRIM_PTRN, ""), radix);
  }

  private static void parseModel(
      final SolverResultBuilder builder,
      final ESExpr model,
      final Context ctx) {
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
    addStandardOperation(StandardOperation.INT2BV, "int2bv");
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

    for (final Function f : standardFunctions()) {
      addCustomOperation(f);
    }

    for (final StandardFunction template : StandardFunction.values()) {
      addCustomOperation(template);
    }
  }

  private static Collection<Function> standardFunctions() {
    final Collection<Function> functions = new ArrayList<>();

    final DataType bit = DataType.BIT_VECTOR(1);

    final Variable xBit = new Variable("x", bit);
    final NodeOperation bv2bool =
        Nodes.eq(new NodeVariable(xBit), NodeValue.newBitVector(BitVector.TRUE));

    functions.add(new Function(StandardOperation.BV2BOOL, DataType.BOOLEAN, bv2bool, xBit));

    final Variable xBool = new Variable("x", DataType.BOOLEAN);
    final NodeOperation bool2bv =
        Nodes.ite(
            new NodeVariable(xBool),
            NodeValue.newBitVector(BitVector.TRUE),
            NodeValue.newBitVector(BitVector.FALSE)
            );

    functions.add(new Function(StandardOperation.BOOL2BV, bit, bool2bv, xBool));
    return functions;
  }
}
