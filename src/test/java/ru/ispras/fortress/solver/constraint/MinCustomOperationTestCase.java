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

import java.util.ArrayList;
import java.util.List;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.StandardOperation;

public class MinCustomOperationTestCase extends GenericSolverTestBase {
  public MinCustomOperationTestCase() {
    super(new MinCustomOperation());
  }

  /**
   * The constraint as described in the SMT language:
   * 
   * <pre>
   *     (declare-const a Real)
   *     (declare-const b Real)
   *     (define-fun MIN ((x Real)(y Real)) Real( ite( >= x y) y x))
   *     (assert( = a( MIN  3.0  4.0)))
   *     (assert( = b( MIN a  2.0)))
   *     (check-sat)
   *     (get-value ( a b))
   *     (exit)
   * </pre>
   * 
   * Expected output:
   * 
   * <pre>
   *     sat ((a 3.0)(b 2.0))
   * </pre>
   */

  public static class MinCustomOperation implements SampleConstraint {
    @Override
    public Constraint getConstraint() {
      final ConstraintBuilder builder = new ConstraintBuilder();

      builder.setName("MinCustomOperation");
      builder.setKind(ConstraintKind.FORMULA_BASED);
      builder.setDescription("MinCustomOperation constraint");

      final NodeVariable a = new NodeVariable(builder.addVariable("a", DataType.REAL));
      final NodeVariable b = new NodeVariable(builder.addVariable("b", DataType.REAL));
      final NodeVariable c = new NodeVariable(builder.addVariable("c", DataType.INTEGER));
      final NodeVariable d = new NodeVariable(builder.addVariable("d", DataType.INTEGER));

      final Formulas formulas = new Formulas();
      builder.setInnerRep(formulas);

      formulas.add(new NodeOperation(StandardOperation.EQ, a, new NodeOperation(
          StandardOperation.MIN, NodeValue.newReal(3.0), NodeValue.newReal(4.0))));

      formulas.add(new NodeOperation(StandardOperation.EQ, b, new NodeOperation(
          StandardOperation.MIN, a, NodeValue.newReal(2.0))));

      formulas.add(new NodeOperation(StandardOperation.EQ, c, new NodeOperation(
          StandardOperation.MIN, NodeValue.newInteger(3), NodeValue.newInteger(4))));

      formulas.add(new NodeOperation(StandardOperation.EQ, d, new NodeOperation(
          StandardOperation.MIN, c, NodeValue.newInteger(2))));

      return builder.build();
    }

    @Override
    public Iterable<Variable> getExpectedVariables() {
      final List<Variable> result = new ArrayList<Variable>();

      result.add(new Variable("a", Data.newReal(3.0)));
      result.add(new Variable("b", Data.newReal(2.0)));
      result.add(new Variable("c", Data.newInteger(3)));
      result.add(new Variable("d", Data.newInteger(2)));

      return result;
    }
  }
}
