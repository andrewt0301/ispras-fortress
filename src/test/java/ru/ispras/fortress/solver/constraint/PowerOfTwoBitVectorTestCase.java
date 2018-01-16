/*
 * Copyright 2012-2017 ISP RAS (http://www.ispras.ru)
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

import java.util.ArrayList;
import java.util.List;

public class PowerOfTwoBitVectorTestCase extends GenericSolverTestBase {
  public PowerOfTwoBitVectorTestCase() {
    super(new PowerOfTwo());
  }

  /**
   * The constraint as described in the SMT-LIB language:
   *
   * <pre>
   * (declare-const x (_ BitVec 32))
   * (assert (bvugt x (_ bv100 32)))
   * (assert (bvult x (_ bv200 32)))
   * (assert (= (bvand x (bvsub x (_ bv1 32))) (_ bv0 32)))
   * (check-sat)
   * (get-value (x))
   * (exit)
   * </pre>
   *
   * Expected output:
   *
   * <pre>
   * sat ((x #x00000080))
   * </pre>
   */
  public static class PowerOfTwo implements SampleConstraint {
    private static final int BIT_VECTOR_SIZE = 32;
    private static final DataType BIT_VECTOR_TYPE = DataType.BIT_VECTOR(BIT_VECTOR_SIZE);

    public Constraint getConstraint() {
      final ConstraintBuilder builder = new ConstraintBuilder();

      builder.setName("PowerOfTwo");
      builder.setKind(ConstraintKind.FORMULA_BASED);
      builder.setDescription("PowerOfTwo constraint");

      final NodeVariable x = new NodeVariable(builder.addVariable("x", BIT_VECTOR_TYPE));

      final Formulas formulas = new Formulas();
      builder.setInnerRep(formulas);

      formulas.add(Nodes.BVUGT(x, new NodeValue(BIT_VECTOR_TYPE.valueOf("100", 10))));
      formulas.add(Nodes.BVULT(x, new NodeValue(BIT_VECTOR_TYPE.valueOf("200", 10))));

      formulas.add(
          Nodes.eq(
              Nodes.BVAND(x, Nodes.bvsub(x, new NodeValue(BIT_VECTOR_TYPE.valueOf("1", 10)))),
              new NodeValue(BIT_VECTOR_TYPE.valueOf("0", 10))));

      return builder.build();
    }

    public Iterable<Variable> getExpectedVariables() {
      final List<Variable> result = new ArrayList<Variable>();
      result.add(new Variable("x", BIT_VECTOR_TYPE.valueOf("128", 10)));
      return result;
    }
  }
}
