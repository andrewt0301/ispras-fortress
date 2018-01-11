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

import java.util.ArrayList;
import java.util.List;

public class ArithmeticTestCase extends GenericSolverTestBase {
  public ArithmeticTestCase() {
    super(new Arithmetic());
  }

  /**
   * The constraint as described in the SMT language:
   *
   * <pre>
   * (declare-const a Int)
   * (declare-const b Int)
   * (declare-const c Int)
   * (declare-const d Real)
   * (declare-const e Real)
   * (assert (> a (+ b 2)))
   * (assert (= a (+ (* 2 c) 10)))
   * (assert (<= (+ c b) 1000))
   * (assert (>= d e))
   * (check-sat)
   * (get-value (a b c d e))
   * (exit)
   * </pre>
   *
   * Expected output: sat ((a 0) (b (- 3)) (c (- 5)) (d 0.0) (e 0.0))
   */
  public static class Arithmetic implements SampleConstraint {
    private static final DataType intType = DataType.INTEGER;
    private static final DataType realType = DataType.REAL;

    @Override
    public Constraint getConstraint() {
      final ConstraintBuilder builder = new ConstraintBuilder();

      builder.setName("Arithmetic");
      builder.setKind(ConstraintKind.FORMULA_BASED);
      builder.setDescription("Arithmetic constraint");

      final NodeVariable a = new NodeVariable(builder.addVariable("a", intType));
      final NodeVariable b = new NodeVariable(builder.addVariable("b", intType));
      final NodeVariable c = new NodeVariable(builder.addVariable("c", intType));
      final NodeVariable d = new NodeVariable(builder.addVariable("d", realType));
      final NodeVariable e = new NodeVariable(builder.addVariable("e", realType));

      final Formulas formulas = new Formulas();
      builder.setInnerRep(formulas);

      formulas.add(Nodes.GREATER(a, Nodes.ADD(b, new NodeValue(intType.valueOf("2", 10)))));

      formulas.add(Nodes.EQ(
          a,
          Nodes.ADD(
              Nodes.MUL(new NodeValue(intType.valueOf("2", 10)), c),
              new NodeValue(intType.valueOf("10", 10)))));

      formulas.add(Nodes.LESSEQ(Nodes.ADD(c, b), new NodeValue(intType.valueOf("1000", 10))));
      formulas.add(Nodes.GREATEREQ(d, e));

      return builder.build();
    }

    @Override
    public Iterable<Variable> getExpectedVariables() {
      final List<Variable> result = new ArrayList<Variable>();

      result.add(new Variable("a", intType.valueOf("0", 10)));
      result.add(new Variable("b", intType.valueOf("-3", 10)));
      result.add(new Variable("c", intType.valueOf("-5", 10)));
      result.add(new Variable("d", realType.valueOf("0.0", 10)));
      result.add(new Variable("e", realType.valueOf("0.0", 10)));

      return result;
    }
  }
}
