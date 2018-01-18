/*
 * Copyright 2016-2018 ISP RAS (http://www.ispras.ru)
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
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
 * Test case checks that both library and jUnit test infrastructure support constraints
 * including unused variables.
 *
 * @author <a href="mailto:smolov@ispras.ru">Sergey Smolov</a>
 */
public class UnusedVariableTestCase extends GenericSolverTestBase {
  public UnusedVariableTestCase() {
    super(new UnusedVariable());
  }

  /**
   * This class constructs a constraint and provides expected values.
   * The constraint as described in the SMT language:
   *
   * <pre>
   * (declare-const x Int)
   * (declare-const y Int)
   * (assert (= x 7))
   * (check-sat)
   * (get-value (x y))
   * (exit)
   * </pre>
   * Expected output: sat ((x 7) (y 0))
   */
  public static class UnusedVariable implements SampleConstraint {
    private static final DataType INT_TYPE = DataType.INTEGER;

    @Override
    public Constraint getConstraint() {
      final ConstraintBuilder builder = new ConstraintBuilder();

      builder.setName("UnusedVariable");
      builder.setKind(ConstraintKind.FORMULA_BASED);
      builder.setDescription("UnusedVariable constraint");

      final NodeVariable x = new NodeVariable(builder.addVariable("x", INT_TYPE));

      /* Here 'y' is a redundant unused variable. */
      builder.addVariable("y", INT_TYPE);

      final Formulas formulas = new Formulas();
      builder.setInnerRep(formulas);

      formulas.add(Nodes.eq(x, NodeValue.newInteger(7)));

      return builder.build();
    }

    @Override
    public Iterable<Variable> getExpectedVariables() {
      final List<Variable> result = new ArrayList<>();

      result.add(new Variable("x", INT_TYPE.valueOf("7", 10)));
      result.add(new Variable("y", INT_TYPE.valueOf("0", 10)));

      return result;
    }
  }
}
