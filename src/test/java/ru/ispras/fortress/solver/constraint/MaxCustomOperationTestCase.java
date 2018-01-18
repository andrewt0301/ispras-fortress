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

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.Nodes;

import java.util.ArrayList;
import java.util.List;

/**
 * This test constructs a constraint, solves it and checks the solution against the expected values.
 * The constraint as described in the SMT language:
 *
 * <pre>
 *     (declare-const a Real)
 *     (declare-const b Real)
 *     (define-fun MAX ((x Real)(y Real)) Real( ite( >= x y) x y))
 *     (assert( = a( MAX  3.0  4.0)))
 *     (assert( = b( MAX a  5.0)))
 *     (check-sat)
 *     (get-value ( a b))
 *     (exit)
 * </pre>
 * Expected output:
 *
 * <pre>
 *     sat ((a 4.0)(b 5.0))
 * </pre>
 */
public class MaxCustomOperationTestCase extends GenericSolverTestBase {
  public MaxCustomOperationTestCase() {
    super(new MaxCustomOperation());
  }

  public static class MaxCustomOperation implements SampleConstraint {
    @Override
    public Constraint getConstraint() {
      final ConstraintBuilder builder = new ConstraintBuilder();

      builder.setName("MaxCustomOperation");
      builder.setKind(ConstraintKind.FORMULA_BASED);
      builder.setDescription("MaxCustomOperation constraint");

      final NodeVariable a = new NodeVariable(builder.addVariable("a", DataType.REAL));
      final NodeVariable b = new NodeVariable(builder.addVariable("b", DataType.REAL));
      final NodeVariable c = new NodeVariable(builder.addVariable("c", DataType.INTEGER));
      final NodeVariable d = new NodeVariable(builder.addVariable("d", DataType.INTEGER));

      final Formulas formulas = new Formulas();
      builder.setInnerRep(formulas);

      formulas.add(Nodes.eq(a, Nodes.max(NodeValue.newReal(3), NodeValue.newReal(4))));
      formulas.add(Nodes.eq(b, Nodes.max(a, NodeValue.newReal(5))));
      formulas.add(Nodes.eq(c, Nodes.max(NodeValue.newInteger(3), NodeValue.newInteger(4))));
      formulas.add(Nodes.eq(d, Nodes.max(c, NodeValue.newInteger(5))));

      return builder.build();
    }

    @Override
    public Iterable<Variable> getExpectedVariables() {
      final List<Variable> result = new ArrayList<Variable>();

      result.add(new Variable("a", Data.newReal(4.0)));
      result.add(new Variable("b", Data.newReal(5.0)));
      result.add(new Variable("c", Data.newInteger(4)));
      result.add(new Variable("d", Data.newInteger(5)));

      return result;
    }
  }
}
