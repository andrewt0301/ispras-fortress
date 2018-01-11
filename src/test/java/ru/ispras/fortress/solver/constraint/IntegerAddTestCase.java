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
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.Nodes;

import java.util.Collections;

public class IntegerAddTestCase extends GenericSolverTestBase {
  public IntegerAddTestCase() {
    super(new IntegerAdd());
  }

  public static class IntegerAdd implements SampleConstraint {
    @Override
    public Constraint getConstraint() {
      final ConstraintBuilder builder = new ConstraintBuilder();

      builder.setName("Arithmetic");
      builder.setKind(ConstraintKind.FORMULA_BASED);
      builder.setDescription("Arithmetic constraint");

      final NodeVariable a = new NodeVariable(builder.addVariable("a", DataType.INTEGER));
      final NodeValue value = new NodeValue(DataType.INTEGER.valueOf("-1487988057", 10));

      builder.setInnerRep(new Formulas(Nodes.EQ(a, Nodes.ADD(value, value))));
      return builder.build();
    }

    @Override
    public Iterable<Variable> getExpectedVariables() {
      return Collections.singletonList(
        new Variable("a", DataType.INTEGER.valueOf("-2975976114", 10)));
    }
  }
}
