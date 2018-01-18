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

/**
 * This test constructs a constraint, solves it and checks the solution against the expected values.
 * The constraint as described in the SMT-LIB language:
 *
 * <pre>
 * (declare-const a Int)
 * (declare-const b Int)
 * (assert (= (~ a) 5))
 * (assert (= (+ b) 1))
 * (check-sat)
 * (get-value (a b))
 * (exit)
 * </pre>
 * Expected output: sat ((x (- 5)) (y 1))
 */
public class UnaryOperationsTestCase extends GenericSolverTestBase {
  public UnaryOperationsTestCase() {
    super(new UnaryOperations());
  }

  public static class UnaryOperations implements SampleConstraint {
    private static final DataType INT_TYPE = DataType.INTEGER;

    @Override
    public Constraint getConstraint() {
      final ConstraintBuilder builder = new ConstraintBuilder();

      builder.setName("UnaryOperations");
      builder.setKind(ConstraintKind.FORMULA_BASED);
      builder.setDescription("Unary Operations constraint");

      final NodeVariable a = new NodeVariable(builder.addVariable("a", INT_TYPE));
      final NodeVariable b = new NodeVariable(builder.addVariable("b", INT_TYPE));

      final Formulas formulas = new Formulas();
      builder.setInnerRep(formulas);

      formulas.add(Nodes.eq(Nodes.minus(a), new NodeValue(INT_TYPE.valueOf("5", 10))));
      formulas.add(Nodes.eq(Nodes.plus(b), new NodeValue(INT_TYPE.valueOf("1", 10))));

      return builder.build();
    }

    @Override
    public Iterable<Variable> getExpectedVariables() {
      final List<Variable> result = new ArrayList<>();

      result.add(new Variable("a", INT_TYPE.valueOf("-5", 10)));
      result.add(new Variable("b", INT_TYPE.valueOf("1", 10)));

      return result;
    }
  }
}
