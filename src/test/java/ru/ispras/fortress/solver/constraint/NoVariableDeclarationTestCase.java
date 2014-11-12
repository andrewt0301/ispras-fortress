/*
 * Copyright 2014 ISP RAS (http://www.ispras.ru)
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
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintBuilder;
import ru.ispras.fortress.solver.constraint.ConstraintKind;
import ru.ispras.fortress.solver.constraint.Formulas;

import java.util.ArrayList;
import java.util.List;

public class NoVariableDeclarationTestCase extends GenericSolverTestBase {
  public NoVariableDeclarationTestCase() {
    super(new NoVariableDeclaration());
  }

  /**
   * The constraint as described in the SMT language:
   * 
   * <pre>
   *     (declare-const a Int)
   *     (declare-const b Int)
   *     (assert (> a (+ b 2)))
   *     (check-sat)
   *     (get-value (a b))
   *     (exit)
   * </pre>
   * 
   * Expected output: sat ((a 1) (b (- 2)))
   */
  public static class NoVariableDeclaration implements SampleConstraint {

    private static final DataType intType = DataType.INTEGER;

    @Override
    public Constraint getConstraint() {
      final ConstraintBuilder builder = new ConstraintBuilder();

      builder.setName("NoVariableDeclaration");
      builder.setKind(ConstraintKind.FORMULA_BASED);
      builder.setDescription("NoVariableDeclaration constraint");

      final NodeVariable a = new NodeVariable(new Variable("a", intType));
      final NodeVariable b = new NodeVariable(new Variable("b", intType));

      final Formulas formulas = new Formulas();
      builder.setInnerRep(formulas);

      formulas.add(new NodeOperation(StandardOperation.GREATER, a, new NodeOperation(
          StandardOperation.ADD, b, new NodeValue(intType.valueOf("2", 10)))));

      // main feature of the test - getting variables declaration from syntax tree
      builder.addVariables(formulas.getVariables());

      return builder.build();
    }

    @Override
    public Iterable<Variable> getExpectedVariables() {
      final List<Variable> result = new ArrayList<Variable>();

      result.add(new Variable("a", intType.valueOf("1", 10)));
      result.add(new Variable("b", intType.valueOf("-2", 10)));

      return result;
    }
  }
}
