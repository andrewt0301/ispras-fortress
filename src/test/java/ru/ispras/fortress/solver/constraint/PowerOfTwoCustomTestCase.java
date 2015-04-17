/*
 * Copyright 2012-2014 ISP RAS (http://www.ispras.ru)
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

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
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.solver.Solver;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintBuilder;
import ru.ispras.fortress.solver.constraint.ConstraintKind;
import ru.ispras.fortress.solver.constraint.Formulas;
import ru.ispras.fortress.solver.function.Function;

public final class PowerOfTwoCustomTestCase extends GenericSolverTestBase {
  public PowerOfTwoCustomTestCase() {
    super(new PowerOfTwoCustom());
  }

  /**
   * The sample is similar to the PowerOfTwo sample, but the is_pow_of_two function is provided as a
   * custom text-based operation that extends the solver.
   * 
   * The constraint as described in the SMT-LIB language:
   * 
   * <pre>
   *     (declare-const x (_ BitVec 32))
   * 
   *     (define-fun is_pow_of_two((a (_ BitVec 32))) Bool (= (bvand a (bvsub a (_ bv1 32))) (_ bv0 32)))
   *     (assert (is_pow_of_two x))
   * 
   *     (assert (bvugt x (_ bv100 32)))
   *     (assert (bvult x (_ bv200 32)))
   * 
   *     (check-sat)
   *     (get-value (x))
   *     (exit)
   * </pre>
   * 
   * Expected output:
   * 
   * <pre>
   *     sat ((x #x00000080))
   * </pre>
   */

  private static final int BIT_VECTOR_SIZE = 32;
  private static final DataType BIT_VECTOR_TYPE = DataType.BIT_VECTOR(BIT_VECTOR_SIZE);
  private static final CalculatorEngine CALCULATOR =
      new CompositeCalculator(Arrays.asList(customCalculator(), Calculator.STANDARD));

  public static enum ECustomOperation {
    ISPOWOFTWO
  }

  @Override
  protected void registerCustomOperations(Solver solver) {
    final Variable param = new Variable("a", BIT_VECTOR_TYPE);

    final Node body =
        new NodeOperation(StandardOperation.EQ, new NodeOperation(StandardOperation.BVAND,
            new NodeVariable(param), new NodeOperation(StandardOperation.BVSUB, new NodeVariable(
                param), new NodeValue(BIT_VECTOR_TYPE.valueOf("1", 10)))), new NodeValue(
            BIT_VECTOR_TYPE.valueOf("0", 10)));

    solver.addCustomOperation(new Function(ECustomOperation.ISPOWOFTWO,
        DataType.BOOLEAN, body, param));
  }

  @Override
  public CalculatorEngine getCalculator() {
    return CALCULATOR;
  }

  private static CalculatorEngine customCalculator() {
    final BitVector ZERO = BitVector.valueOf(0, BIT_VECTOR_SIZE);
    final BitVector ONE = BitVector.valueOf(1, BIT_VECTOR_SIZE);

    final CalculatorOperation<ECustomOperation> ispot =
        new CalculatorOperation<ECustomOperation>(
            ECustomOperation.ISPOWOFTWO, ArityRange.UNARY) {
          @Override
          public Data calculate(Data... operands) {
            final BitVector x = operands[0].getBitVector();
            final BitVector test =
                BitVectorMath.and(x, BitVectorMath.sub(x, ONE));
            return Data.newBoolean(test.equals(ZERO));
          }
    };

    final OperationGroup<ECustomOperation> group = new OperationGroup<>();
    final List<? extends Operation<ECustomOperation>> operations =
        Collections.singletonList(ispot);

    group.registerOperations(
        DataTypeId.BIT_VECTOR,
        OperationGroup.operationMap(ECustomOperation.class, operations));

    return group;
  }

  public static class PowerOfTwoCustom implements SampleConstraint {
    public Constraint getConstraint() {
      final ConstraintBuilder builder = new ConstraintBuilder();

      builder.setName("PowerOfTwoCustomText");
      builder.setKind(ConstraintKind.FORMULA_BASED);
      builder.setDescription("PowerOfTwoCustomText constraint");

      final NodeVariable x = new NodeVariable(builder.addVariable("x", BIT_VECTOR_TYPE));

      final Formulas formulas = new Formulas();
      builder.setInnerRep(formulas);

      formulas.add(new NodeOperation(StandardOperation.BVUGT, x, new NodeValue(BIT_VECTOR_TYPE
          .valueOf("100", 10))));

      formulas.add(new NodeOperation(StandardOperation.BVULT, x, new NodeValue(BIT_VECTOR_TYPE
          .valueOf("200", 10))));

      formulas.add(new NodeOperation(ECustomOperation.ISPOWOFTWO, x));

      return builder.build();
    }

    public Iterable<Variable> getExpectedVariables() {
      final List<Variable> result = new ArrayList<Variable>();

      result.add(new Variable("x", BIT_VECTOR_TYPE.valueOf("128", 10)));

      return result;
    }
  }
}
