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

import java.util.Collections;

import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.NodeValue;

public class NoVariableTestCase extends GenericSolverTestBase {
  public NoVariableTestCase() {
    super(new NoVariable());
  }

  /**
   * The constraint as described in the SMT language:
   * 
   * <pre>
   *      (assert true)
   *      (check-sat)
   *      (exit)
   * </pre>
   * 
   * Expected output:
   * 
   * <pre>
   * sat
   * </pre>
   */

  public static class NoVariable implements SampleConstraint {
    @Override
    public Constraint getConstraint() {
      final ConstraintBuilder builder = new ConstraintBuilder();

      builder.setName("NoVariable");
      builder.setKind(ConstraintKind.FORMULA_BASED);
      builder.setDescription("NoVariable constraint");

      final Formulas formulas = new Formulas(NodeValue.newBoolean(true));
      builder.setInnerRep(formulas);

      return builder.build();
    }

    @Override
    public Iterable<Variable> getExpectedVariables() {
      return Collections.emptyList();
    }
  }
}
