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

public class IfThenElseTestCase extends GenericSolverTestBase {
  public IfThenElseTestCase() {
    super(new IfThenElse());
  }

  /**
   * The constraint as described in the SMT language:
   *
   * <pre>
   * (declare-const a Int)
   * (declare-const b Int)
   * (assert (> a 5))
   * (assert (< b 7))
   * (assert (= (ite (= a b) 1 0) 1))
   * (check-sat)
   * (get-value (a b))
   * (exit)
   * </pre>
   *
   * Expected output:
   *
   * <pre>
   * sat ((a 6)(b 6))
   * </pre>
   */
  public static class IfThenElse implements SampleConstraint {
    private static final DataType intType = DataType.INTEGER;

    @Override
    public Constraint getConstraint() {
      final ConstraintBuilder builder = new ConstraintBuilder();

      builder.setName("IfThenElse");
      builder.setKind(ConstraintKind.FORMULA_BASED);
      builder.setDescription("IfThenElse constraint");

      final NodeVariable a = new NodeVariable(builder.addVariable("a", intType));
      final NodeVariable b = new NodeVariable(builder.addVariable("b", intType));

      final Formulas formulas = new Formulas();
      builder.setInnerRep(formulas);

      formulas.add(Nodes.GREATER(a, new NodeValue(intType.valueOf("5", 10))));
      formulas.add(Nodes.LESS(b, new NodeValue(intType.valueOf("7", 10))));

      formulas.add(Nodes.eq(
          Nodes.ite(
              Nodes.eq(a, b),
              new NodeValue(intType.valueOf("1", 10)),
              new NodeValue(intType.valueOf("0", 10))),
          new NodeValue(intType.valueOf("1", 10)))
      );

      return builder.build();
    }

    @Override
    public Iterable<Variable> getExpectedVariables() {
      final List<Variable> result = new ArrayList<Variable>();

      result.add(new Variable("a", intType.valueOf("6", 10)));
      result.add(new Variable("b", intType.valueOf("6", 10)));

      return result;
    }
  }
}
