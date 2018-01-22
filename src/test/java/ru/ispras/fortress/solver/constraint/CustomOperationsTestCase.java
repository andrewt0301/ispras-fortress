/*
 * Copyright 2012-2018 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.solver.constraint;

import ru.ispras.fortress.calculator.ArityRange;
import ru.ispras.fortress.calculator.Calculator;
import ru.ispras.fortress.calculator.CalculatorEngine;
import ru.ispras.fortress.calculator.CalculatorOperation;
import ru.ispras.fortress.calculator.CompositeCalculator;
import ru.ispras.fortress.calculator.Operation;
import ru.ispras.fortress.calculator.OperationGroup;
import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.DataTypeId;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.data.types.bitvector.BitVector;
import ru.ispras.fortress.data.types.bitvector.BitVectorMath;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.Nodes;
import ru.ispras.fortress.solver.Solver;
import ru.ispras.fortress.solver.function.Function;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

public class CustomOperationsTestCase extends GenericSolverTestBase {
  private static final CalculatorEngine CALCULATOR =
      new CompositeCalculator(Arrays.asList(customCalculator(), Calculator.STANDARD));

  public CustomOperationsTestCase() {
    super(new CustomOperations());
  }

  /**
   * The semantics of SMT code is the same as with the integer overflow example, but in our case we
   * use custom functions.
   *
   * <p>The constraint as described in the SMT language:
   *
   * <pre>
   * (define-sort        Int_t () (_ BitVec 64))
   *
   * (define-fun      INT_ZERO () Int_t (_ bv0 64))
   * (define-fun INT_BASE_SIZE () Int_t (_ bv32 64))
   * (define-fun INT_SIGN_MASK () Int_t (bvshl (bvnot INT_ZERO) INT_BASE_SIZE))
   *
   * (define-fun IsValidPos ((x!1 Int_t)) Bool
   * (ite (= (bvand x!1 INT_SIGN_MASK) INT_ZERO) true false))
   * (define-fun IsValidNeg ((x!1 Int_t)) Bool
   * (ite (= (bvand x!1 INT_SIGN_MASK) INT_SIGN_MASK) true false))
   * (define-fun IsValidSignedInt ((x!1 Int_t)) Bool
   * (ite (or (IsValidPos x!1) (IsValidNeg x!1)) true false))
   *
   * (declare-const rs Int_t)
   * (declare-const rt Int_t)
   *
   * ; rt and rs must contain valid sign-extended 32-bit values (bits 63..31 equal)
   * (assert (IsValidSignedInt rs))
   * (assert (IsValidSignedInt rt))
   *
   * ; the condition for an overflow: the summation result is not a valid sign-extended 32-bit value
   * (assert (not (IsValidSignedInt (bvadd rs rt))))
   *
   * ; just in case: rs and rt are not equal (to make the results more interesting)
   * (assert (not (= rs rt)))
   *
   * (check-sat)
   *
   * (echo "Values that lead to an overflow:")
   * (get-value (rs rt))
   * </pre>
   * Expected output (values that lead to an overflow):
   *
   * <pre>
   * sat ((rs #x000000009b91b193) (rt #x000000009b91b1b3))
   * </pre></p>
   */
  private static final int BV_LENGTH = 64;
  private static final DataType INT_T = DataType.bitVector(BV_LENGTH);

  enum ECustomOperation {
      INT_ZERO, INT_BASE_SIZE, INT_SIGN_MASK, IS_VALID_POS, IS_VALID_NEG, IS_VALID_SIGNED_INT
  }

  @Override
  protected void registerCustomOperations(final Solver solver) {
    registerIntZero(solver);
    registerIntBaseSize(solver);
    registerIntSignMask(solver);
    registerIsValidPos(solver);
    registerIsValidNeg(solver);
    registerIsValidSignedInt(solver);
  }

  // (define-fun INT_ZERO () Int_t (_ bv0 64))
  private void registerIntZero(final Solver solver) {
    final Node body = new NodeValue(INT_T.valueOf("0", 10));
    solver.addCustomOperation(new Function(ECustomOperation.INT_ZERO, INT_T, body));
  }

  // (define-fun INT_BASE_SIZE () Int_t (_ bv32 64))
  private void registerIntBaseSize(final Solver solver) {
    final Node body = new NodeValue(INT_T.valueOf("32", 10));
    solver.addCustomOperation(new Function(ECustomOperation.INT_BASE_SIZE, INT_T, body));
  }

  // (define-fun INT_SIGN_MASK () Int_t (bvshl (bvnot INT_ZERO) INT_BASE_SIZE))
  private void registerIntSignMask(final Solver solver) {
    final Node body = Nodes.bvlshl(
        Nodes.bvnot(new NodeOperation(ECustomOperation.INT_ZERO)),
        new NodeOperation(ECustomOperation.INT_BASE_SIZE));

    solver.addCustomOperation(new Function(ECustomOperation.INT_SIGN_MASK, INT_T, body));
  }

  // (define-fun IS_VALID_POS ((x!1 Int_t)) Bool (ite (= (bvand x!1 INT_SIGN_MASK) INT_ZERO) true
  // false))
  private void registerIsValidPos(final Solver solver) {
    final Variable param = new Variable("x", INT_T);

    final Node body = Nodes.eq(
        Nodes.bvand(new NodeVariable(param), new NodeOperation(ECustomOperation.INT_SIGN_MASK)),
        new NodeOperation(ECustomOperation.INT_ZERO));

    solver.addCustomOperation(new Function(
        ECustomOperation.IS_VALID_POS, DataType.BOOLEAN, body, param));
  }

  // (define-fun IS_VALID_NEG ((x!1 Int_t)) Bool (ite (= (bvand x!1 INT_SIGN_MASK) INT_SIGN_MASK)
  // true false))
  private void registerIsValidNeg(final Solver solver) {
    final Variable param = new Variable("x", INT_T);

    final Node body = Nodes.eq(
        Nodes.bvand(new NodeVariable(param), new NodeOperation(ECustomOperation.INT_SIGN_MASK)),
        new NodeOperation(ECustomOperation.INT_SIGN_MASK));

    solver.addCustomOperation(
        new Function(ECustomOperation.IS_VALID_NEG, DataType.BOOLEAN, body, param));
  }

  // (define-fun IS_VALID_SIGNED_INT ((x!1 Int_t)) Bool (ite (or (IsValidPos x!1) (IsValidNeg
  // x!1)) true false))
  private void registerIsValidSignedInt(final Solver solver) {
    final Variable param = new Variable("x", INT_T);

    final Node body = Nodes.or(
        new NodeOperation(ECustomOperation.IS_VALID_POS, new NodeVariable(param)),
        new NodeOperation(ECustomOperation.IS_VALID_NEG, new NodeVariable(param)));

    solver.addCustomOperation(
        new Function(ECustomOperation.IS_VALID_SIGNED_INT, DataType.BOOLEAN, body, param));
  }

  public static class CustomOperations implements SampleConstraint {
    @Override
    public Constraint getConstraint() {
      final ConstraintBuilder builder = new ConstraintBuilder();

      builder.setName("CustomOpIntegerOverflow");
      builder.setKind(ConstraintKind.FORMULA_BASED);
      builder.setDescription("Custom Operation IntegerOverflow constraint");

      // Unknown variables

      // (declare-const rs Int_t)
      final NodeVariable rs = new NodeVariable(builder.addVariable("rs", INT_T));
      // (declare-const rt Int_t)
      final NodeVariable rt = new NodeVariable(builder.addVariable("rt", INT_T));

      final Formulas formulas = new Formulas();
      builder.setInnerRep(formulas);

      // ; rt and rs must contain valid sign-extended 32-bit values (bits 63..31 equal)

      // (assert (IsValidSignedInt rs))
      formulas.add(new NodeOperation(ECustomOperation.IS_VALID_SIGNED_INT, rs));

      // (assert (IsValidSignedInt rt))
      formulas.add(new NodeOperation(ECustomOperation.IS_VALID_SIGNED_INT, rt));

      // ; the condition for an overflow: the summation result is not a valid sign-extended 32-bit
      // value

      // (assert (not (IsValidSignedInt (bvadd rs rt))))
      formulas.add(Nodes.not(
          new NodeOperation(ECustomOperation.IS_VALID_SIGNED_INT, Nodes.bvadd(rs, rt))));

      // ; just in case: rs and rt are not equal (to make the results more interesting)
      // (assert (not (= rs rt)))

      formulas.add(Nodes.not(Nodes.eq(rs, rt)));
      return builder.build();
    }

    @Override
    public Iterable<Variable> getExpectedVariables() {
      final List<Variable> result = new ArrayList<>();

      result.add(new Variable("rs", INT_T.valueOf("000000009b91b193", 16)));
      result.add(new Variable("rt", INT_T.valueOf("000000009b91b1b3", 16)));

      return result;
    }
  }

  private static CalculatorEngine customCalculator() {
    final BitVector zero = BitVector.valueOf(0, 64);
    final BitVector mask = BitVectorMath.shl(BitVectorMath.not(zero), 32);

    final CalculatorOperation<ECustomOperation> validSigned =
        new CalculatorOperation<ECustomOperation>(
            ECustomOperation.IS_VALID_SIGNED_INT, ArityRange.UNARY) {
          @Override
          public Data calculate(final Data... operands) {
            final BitVector bv = BitVectorMath.and(operands[0].getBitVector(), mask);
            return Data.newBoolean(bv.equals(mask) || bv.equals(zero));
          }
    };

    final OperationGroup<ECustomOperation> group = new OperationGroup<>();
    final List<? extends Operation<ECustomOperation>> operations =
        Collections.singletonList(validSigned);

    group.registerOperations(
        DataTypeId.BIT_VECTOR,
        OperationGroup.newOperationMap(ECustomOperation.class, operations));

    return group;
  }

  @Override
  protected CalculatorEngine getCalculator() {
    return CALCULATOR;
  }
}
