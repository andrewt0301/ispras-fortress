/*
 * Copyright 2017-2018 ISP RAS (http://www.ispras.ru)
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
import ru.ispras.fortress.data.types.bitvector.BitVector;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.Nodes;

import java.util.ArrayList;
import java.util.List;

public class IntToBvTestCase extends GenericSolverTestBase {
  public IntToBvTestCase() {
    super(new IntToBvOperation());
  }

  /**
   * The constraint as described in the SMT language:
   *
   * <pre>
   * (declare-const x Int)
   * (assert (= ((_ int2bv 2) x) #b11))
   * (check-sat)
   * (get-model)
   * (get-value (x ))
   * (exit)
   * </pre>
   * Expected output: sat (x 3)
   */
  public static class IntToBvOperation implements SampleConstraint {
    private static final DataType INT_TYPE = DataType.INTEGER;
    private static final int BIT_VECTOR_SIZE = 2;
    private static final int RADIX = 2;

    @Override
    public Constraint getConstraint() {
      final ConstraintBuilder builder = new ConstraintBuilder();

      builder.setName("IntToBv");
      builder.setKind(ConstraintKind.FORMULA_BASED);
      builder.setDescription("IntToBv constraint");

      final NodeVariable x = new NodeVariable(builder.addVariable("x", INT_TYPE));

      final Formulas formulas = new Formulas();
      builder.setInnerRep(formulas);

      formulas.add(
          Nodes.eq(
              Nodes.int2bv(
                  NodeValue.newInteger(BIT_VECTOR_SIZE), x),
                  NodeValue.newBitVector(BitVector.valueOf("11", RADIX, BIT_VECTOR_SIZE))));

      return builder.build();
    }

    @Override
    public Iterable<Variable> getExpectedVariables() {
      final List<Variable> result = new ArrayList<>();
      result.add(new Variable("x", INT_TYPE.valueOf("3", 10)));
      return result;
    }
  }
}
