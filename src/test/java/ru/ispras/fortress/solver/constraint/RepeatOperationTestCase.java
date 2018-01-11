/*
 * Copyright 2014-2017 ISP RAS (http://www.ispras.ru)
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

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.Nodes;
import ru.ispras.fortress.transformer.ReduceOptions;
import ru.ispras.fortress.transformer.Reducer;

import java.util.ArrayList;
import java.util.List;

public final class RepeatOperationTestCase extends GenericSolverTestBase {
  public RepeatOperationTestCase() {
    super(new RepeatOperation());
  }

  /**
   * The constraint as described in the SMT language:
   *
   * <pre>
   * (declare-const x (_ BitVec 4))
   * (declare-const y (_ BitVec 16))
   * (assert (= x #x5))
   * (assert (= y ((_ repeat 4) x)))
   * (check-sat)
   * (get-value (x y))
   * (exit)
   * </pre>
   *
   * Expected output: sat ((x #x5)(y #x5555))
   */
  public static class RepeatOperation implements SampleConstraint {
    private static final int BIT_VECTOR_ARG_SIZE = 4;
    private static final DataType BIT_VECTOR_ARG_TYPE = DataType.BIT_VECTOR(BIT_VECTOR_ARG_SIZE);
    private static final int BIT_VECTOR_RES_SIZE = 16;
    private static final DataType BIT_VECTOR_RES_TYPE = DataType.BIT_VECTOR(BIT_VECTOR_RES_SIZE);
    private static final DataType INT_TYPE = DataType.INTEGER;

    private static final int HEX_RADIX = 16;
    private static final int DEC_RADIX = 10;

    @Override
    public Constraint getConstraint() {
      final ConstraintBuilder builder = new ConstraintBuilder();

      builder.setName("RepeatOperation");
      builder.setKind(ConstraintKind.FORMULA_BASED);
      builder.setDescription("RepeatOperation constraint");

      final NodeVariable x = new NodeVariable(builder.addVariable("x", BIT_VECTOR_ARG_TYPE));
      final NodeVariable y = new NodeVariable(builder.addVariable("y", BIT_VECTOR_RES_TYPE));

      final Formulas formulas = new Formulas();
      builder.setInnerRep(formulas);

      formulas.add(Nodes.EQ(x, new NodeValue(BIT_VECTOR_ARG_TYPE.valueOf("5", HEX_RADIX))));
      formulas.add(Nodes.EQ(
          y,
          Nodes.BVREPEAT(
              (NodeValue) Reducer.reduce(
                  ReduceOptions.NEW_INSTANCE,
                  Nodes.ADD(new NodeValue(INT_TYPE.valueOf("2", DEC_RADIX)),
                            new NodeValue(INT_TYPE.valueOf("2", DEC_RADIX)))),
              x)));

      return builder.build();
    }

    @Override
    public Iterable<Variable> getExpectedVariables() {
      final List<Variable> result = new ArrayList<Variable>();

      result.add(new Variable("x", BIT_VECTOR_ARG_TYPE.valueOf("5", HEX_RADIX)));
      result.add(new Variable("y", BIT_VECTOR_RES_TYPE.valueOf("5555", HEX_RADIX)));

      return result;
    }
  }
}
