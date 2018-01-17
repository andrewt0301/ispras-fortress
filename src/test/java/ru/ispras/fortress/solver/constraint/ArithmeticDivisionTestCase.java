/*
 * Copyright 2014-2018 ISP RAS (http://www.ispras.ru)
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

public class ArithmeticDivisionTestCase extends GenericSolverTestBase {
  public ArithmeticDivisionTestCase() {
    super(new ArithmeticDivision());
  }

  /**
   * The constraint as described in the SMT language:
   *
   * <pre>
   * (declare-const a Int)
   * (declare-const r1 Int)
   * (declare-const r2 Int)
   * (declare-const r3 Int)
   * (declare-const r4 Int)
   * (declare-const r5 Int)
   * (declare-const r6 Int)
   * (assert (= a 10))
   * (assert (= r1 (div a 4)))
   * (assert (= r2 (mod a 4)))
   * (assert (= r3 (rem a 4)))
   * (assert (= r4 (div a (- 4))))
   * (assert (= r5 (mod a (- 4))))
   * (assert (= r6 (rem a (- 4))))
   * (check-sat)
   * (get-value (a r1 r2 r3 r4 r5 r6))
   * (exit)
   * </pre>
   * Expected output: sat ((a 10) (r1 2) (r2 2) (r3 2) (r4 (- 2)) (r5 2) (r6 (- 2)))
   */
  public static class ArithmeticDivision implements SampleConstraint {
    private static final DataType intType = DataType.INTEGER;

    @Override
    public Constraint getConstraint() {
      final ConstraintBuilder builder = new ConstraintBuilder();

      builder.setName("ArithmeticDivision");
      builder.setDescription("ArithmeticDivision constraint");
      builder.setKind(ConstraintKind.FORMULA_BASED);

      final NodeVariable a = new NodeVariable(builder.addVariable("a", intType));
      final NodeVariable r1 = new NodeVariable(builder.addVariable("r1", intType));
      final NodeVariable r2 = new NodeVariable(builder.addVariable("r2", intType));
      final NodeVariable r3 = new NodeVariable(builder.addVariable("r3", intType));
      final NodeVariable r4 = new NodeVariable(builder.addVariable("r4", intType));
      final NodeVariable r5 = new NodeVariable(builder.addVariable("r5", intType));
      final NodeVariable r6 = new NodeVariable(builder.addVariable("r6", intType));

      final Formulas formulas = new Formulas();
      builder.setInnerRep(formulas);

      formulas.add(Nodes.eq(a, new NodeValue(intType.valueOf("10", 10))));

      formulas.add(Nodes.eq(r1, Nodes.div(a, new NodeValue(intType.valueOf("4", 10)))));
      formulas.add(Nodes.eq(r2, Nodes.mod(a, new NodeValue(intType.valueOf("4", 10)))));
      formulas.add(Nodes.eq(r3, Nodes.rem(a, new NodeValue(intType.valueOf("4", 10)))));
      formulas.add(Nodes.eq(r4, Nodes.div(a, new NodeValue(intType.valueOf("-4", 10)))));
      formulas.add(Nodes.eq(r5, Nodes.mod(a, new NodeValue(intType.valueOf("-4", 10)))));
      formulas.add(Nodes.eq(r6, Nodes.rem(a, new NodeValue(intType.valueOf("-4", 10)))));

      return builder.build();
    }

    @Override
    public Iterable<Variable> getExpectedVariables() {
      final List<Variable> result = new ArrayList<>();

      result.add(new Variable("a", intType.valueOf("10", 10)));
      result.add(new Variable("r1", intType.valueOf("2", 10)));
      result.add(new Variable("r2", intType.valueOf("2", 10)));
      result.add(new Variable("r3", intType.valueOf("2", 10)));
      result.add(new Variable("r4", intType.valueOf("-2", 10)));
      result.add(new Variable("r5", intType.valueOf("2", 10)));
      result.add(new Variable("r6", intType.valueOf("-2", 10)));

      return result;
    }
  }
}
