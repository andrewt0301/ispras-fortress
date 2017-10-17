/*
 * Copyright 2014-2017 ISP RAS (http://www.ispras.ru)
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless rNodes.EQuired by applicable law or agreed to in writing, software distributed under the License
 * is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
 * or implied. See the License for the specific language governing permissions and limitations under
 * the License.
 */

package ru.ispras.fortress.solver.constraint;

import java.util.ArrayList;

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.*;

/**
 * The constraint as described in the SMT-LIB language:
 * 
 * <pre>
 * (define-sort ARRAY_INT_INT () (Array Int Int))
 * (define-sort ARRAY_COMPOSITE () (Array ARRAY_INT_INT ARRAY_INT_INT))
 * (declare-fun x () ARRAY_INT_INT)
 * (declare-fun y () ARRAY_INT_INT)
 * (declare-fun z () ARRAY_INT_INT)
 * (declare-fun w () ARRAY_INT_INT)
 * (declare-fun u () ARRAY_COMPOSITE)
 * (declare-fun v () ARRAY_COMPOSITE)
 *
 * (assert (= x (Nodes.STORE x -1 -1)))
 * (assert (= y (Nodes.STORE x 0 0)))
 * (assert (= z (Nodes.STORE y 1 2)))
 * (assert (= w (Nodes.STORE z 3 4)))
 *
 * (assert (= u (Nodes.STORE u x y)))
 * (assert (= v (Nodes.STORE u z w)))
 *
 * (check-sat)
 * (get-model)
 * </pre>
 */
public class ArrayOfArraysTestCase extends GenericSolverTestBase {
  public ArrayOfArraysTestCase() {
    super(new ArrayOfArraysConstraint());
  }

  private final static class ArrayOfArraysConstraint implements SampleConstraint {
    private static final DataType ARRAY_INT_INT = DataType.MAP(DataType.INTEGER, DataType.INTEGER);
    private static final DataType ARRAY_COMPOSITE = DataType.MAP(ARRAY_INT_INT, ARRAY_INT_INT);

    public Constraint getConstraint() {
      final ConstraintBuilder builder = new ConstraintBuilder();

      builder.setName("ArrayOfArrays");
      builder.setKind(ConstraintKind.FORMULA_BASED);
      builder.setDescription("ArrayOfArrays constraint");

      final NodeVariable x = new NodeVariable(builder.addVariable("x", ARRAY_INT_INT));
      final NodeVariable y = new NodeVariable(builder.addVariable("y", ARRAY_INT_INT));
      final NodeVariable z = new NodeVariable(builder.addVariable("z", ARRAY_INT_INT));
      final NodeVariable w = new NodeVariable(builder.addVariable("w", ARRAY_INT_INT));
      final NodeVariable u = new NodeVariable(builder.addVariable("u", ARRAY_COMPOSITE));
      final NodeVariable v = new NodeVariable(builder.addVariable("v", ARRAY_COMPOSITE));

      final NodeValue[] values = new NodeValue[6];
      for (int i = 0; i < values.length; ++i) {
        values[i] = new NodeValue(DataType.INTEGER.valueOf(Integer.toString(i - 1, 10), 10));
      }

      final Formulas formulas = new Formulas();
      builder.setInnerRep(formulas);

      formulas.add(Nodes.EQ(x, Nodes.STORE(x, values[0], values[0])));
      formulas.add(Nodes.EQ(y, Nodes.STORE(x, values[1], values[1])));
      formulas.add(Nodes.EQ(z, Nodes.STORE(y, values[2], values[3])));
      formulas.add(Nodes.EQ(w, Nodes.STORE(z, values[4], values[5])));

      formulas.add(Nodes.EQ(u, Nodes.STORE(u, x, y)));
      formulas.add(Nodes.EQ(v, Nodes.STORE(u, z, w)));

      return builder.build();
    }

    public Iterable<Variable> getExpectedVariables() {
      final String xValue = "((-1:-1)(0:8)(1:7)(3:6))";
      final String yValue = "((-1:-1)(0:0)(1:7)(3:6))";
      final String zValue = "((-1:-1)(0:0)(1:2)(3:6))";
      final String wValue = "((-1:-1)(0:0)(1:2)(3:4))";
      final String uValue = String.format("((%s:%s))", xValue, yValue);
      final String vValue = String.format("((%s:%s)(%s:%s))", xValue, yValue, zValue, wValue);

      final ArrayList<Variable> list = new ArrayList<Variable>(6);

      list.add(new Variable("x", ARRAY_INT_INT.valueOf(xValue, 10)));
      list.add(new Variable("y", ARRAY_INT_INT.valueOf(yValue, 10)));
      list.add(new Variable("z", ARRAY_INT_INT.valueOf(zValue, 10)));
      list.add(new Variable("w", ARRAY_INT_INT.valueOf(wValue, 10)));
      list.add(new Variable("u", ARRAY_COMPOSITE.valueOf(uValue, 10)));
      list.add(new Variable("v", ARRAY_COMPOSITE.valueOf(vValue, 10)));

      return list;
    }
  }
}
