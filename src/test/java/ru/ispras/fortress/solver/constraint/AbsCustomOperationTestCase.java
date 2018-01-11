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

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.Nodes;

import java.util.ArrayList;
import java.util.List;

public class AbsCustomOperationTestCase extends GenericSolverTestBase {
  public AbsCustomOperationTestCase() {
    super(new AbsCustomOperation());
  }

  /**
   * The constraint as described in the SMT language:
   *
   * <pre>
   *     (declare-const a Real)
   *     (declare-const b Real)
   *     (declare-const c Int)
   *     (declare-const d Int)
   *     (define-fun StandardOperation_ABS_RET_LOGIC_REAL_PARAMS_LOGIC_REAL ((x Real)) Real (ite (>= x 0.0) x (- x)))
   *     (define-fun StandardOperation_ABS_RET_LOGIC_INTEGER_PARAMS_LOGIC_INTEGER ((x Int)) Int (ite (>= x 0) x (- x)))
   *     (assert  (< a 0.0))
   *     (assert  (> b 0.0))
   *     (assert  (< c 0))
   *     (assert  (> d 0))
   *     (assert  (= (StandardOperation_ABS_RET_LOGIC_REAL_PARAMS_LOGIC_REAL (- 5.0)) 5.0))
   *     (assert  (= (StandardOperation_ABS_RET_LOGIC_REAL_PARAMS_LOGIC_REAL 5.0) 5.0))
   *     (assert  (= (StandardOperation_ABS_RET_LOGIC_REAL_PARAMS_LOGIC_REAL (- a)) 5.0))
   *     (assert  (= (StandardOperation_ABS_RET_LOGIC_REAL_PARAMS_LOGIC_REAL b) 5.0))
   *     (assert  (= (StandardOperation_ABS_RET_LOGIC_INTEGER_PARAMS_LOGIC_INTEGER (- c)) 5))
   *     (assert  (= (StandardOperation_ABS_RET_LOGIC_INTEGER_PARAMS_LOGIC_INTEGER d) 5))
   *     (check-sat)
   *     (get-value ( a b c d))
   *     (get-model)
   *     (exit)
   * </pre>
   *
   * Expected output: sat ((a (- 5.0)) (b 5.0) (c (- 5)) (d 5))
   */

  public static class AbsCustomOperation implements SampleConstraint {
    @Override
    public Constraint getConstraint() {
      final ConstraintBuilder builder = new ConstraintBuilder();

      builder.setName("AbsCustomOperation");
      builder.setKind(ConstraintKind.FORMULA_BASED);
      builder.setDescription("AbsCustomOperation constraint");

      final NodeVariable a = new NodeVariable(builder.addVariable("a", DataType.REAL));
      final NodeVariable b = new NodeVariable(builder.addVariable("b", DataType.REAL));
      final NodeVariable c = new NodeVariable(builder.addVariable("c", DataType.INTEGER));
      final NodeVariable d = new NodeVariable(builder.addVariable("d", DataType.INTEGER));

      final Formulas formulas = new Formulas();
      builder.setInnerRep(formulas);

      formulas.add(Nodes.LESS(a, NodeValue.newReal(0)));
      formulas.add(Nodes.GREATER(b, NodeValue.newReal(0)));
      formulas.add(Nodes.LESS(c, NodeValue.newInteger(0)));
      formulas.add(Nodes.GREATER(d, NodeValue.newInteger(0)));

      formulas.add(Nodes.EQ(
          Nodes.ABS(Nodes.MINUS(NodeValue.newReal(5.0))), NodeValue.newReal(5.0)));

      formulas.add(Nodes.EQ(
          Nodes.ABS(NodeValue.newReal(5.0)), NodeValue.newReal(5.0)));

      formulas.add(Nodes.EQ(
          Nodes.ABS(Nodes.MINUS(a)), NodeValue.newReal(5.0)));

      formulas.add(Nodes.EQ(
          Nodes.ABS(b), NodeValue.newReal(5.0)));

      formulas.add(Nodes.EQ(
          Nodes.ABS(Nodes.MINUS(c)), NodeValue.newInteger(5)));

      formulas.add(Nodes.EQ(
          Nodes.ABS(d), NodeValue.newInteger(5)));

      return builder.build();
    }

    @Override
    public Iterable<Variable> getExpectedVariables() {
      final List<Variable> result = new ArrayList<Variable>();

      result.add(new Variable("a", Data.newReal(-5.0)));
      result.add(new Variable("b", Data.newReal(5.0)));
      result.add(new Variable("c", Data.newInteger(-5)));
      result.add(new Variable("d", Data.newInteger(5)));

      return result;
    }
  }
}
