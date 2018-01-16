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

public final class SimpleBitVectorTestCase extends GenericSolverTestBase {
  public SimpleBitVectorTestCase() {
    super(new SimpleBitVector());
  }

  /**
   * The constraint as described in the SMT language:
   *
   * <pre>
   * (declare-const a (_ BitVec 3))
   * (declare-const b (_ BitVec 3))
   * (assert (not (= a b)))
   * (assert (= (bvor a b) #b111))
   * (assert (= (bvand a b) #b000))
   * (assert (= (bvshl a (_ bv3 3))(bvsmod a (_ bv2 3))))
   * (check-sat)
   * (get-value (a b))
   * (exit)
   * </pre>
   *
   * Expected output: sat ((a #b010) (b #b101))
   */
  public static class SimpleBitVector implements SampleConstraint {
    private static final int BIT_VECTOR_SIZE = 3;
    private static final DataType BIT_VECTOR_TYPE = DataType.BIT_VECTOR(BIT_VECTOR_SIZE);

    @Override
    public Constraint getConstraint() {
      final ConstraintBuilder builder = new ConstraintBuilder();

      builder.setName("SimpleBitVector");
      builder.setKind(ConstraintKind.FORMULA_BASED);
      builder.setDescription("SimpleBitVector constraint");

      final NodeVariable a = new NodeVariable(builder.addVariable("a", BIT_VECTOR_TYPE));
      final NodeVariable b = new NodeVariable(builder.addVariable("b", BIT_VECTOR_TYPE));

      final Formulas formulas = new Formulas();
      builder.setInnerRep(formulas);

      formulas.add(Nodes.not(Nodes.eq(a, b)));
      formulas.add(Nodes.eq(Nodes.bvor(a, b), new NodeValue(BIT_VECTOR_TYPE.valueOf("111", 2))));

      formulas.add(Nodes.eq(
          Nodes.bvlshl(a, new NodeValue(BIT_VECTOR_TYPE.valueOf("3", 10))),
          Nodes.bvsmod(a, new NodeValue(BIT_VECTOR_TYPE.valueOf("2", 10)))));

      formulas.add(Nodes.eq(Nodes.BVAND(a, b), new NodeValue(BIT_VECTOR_TYPE.valueOf("0", 2))));

      return builder.build();
    }

    @Override
    public Iterable<Variable> getExpectedVariables() {
      final List<Variable> result = new ArrayList<Variable>();

      result.add(new Variable("a", BIT_VECTOR_TYPE.valueOf("010", 2)));
      result.add(new Variable("b", BIT_VECTOR_TYPE.valueOf("101", 2)));

      return result;
    }
  }
}
