/*
 * Copyright (c) 2014 ISPRAS (www.ispras.ru)
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * IntegerAddTestCase.java, Aug 5, 2014 5:03:35 PM Andrei Tatarnikov
 * 
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not
 * use this file except in compliance with the License. You may obtain a copy of
 * the License at
 * 
 * http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations under
 * the License.
 */

package ru.ispras.fortress.solver.constraint;

import java.util.Collections;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.StandardOperation;

public class IntegerAddTestCase extends GenericSolverTestBase
{
    public IntegerAddTestCase()
    {
        super(new IntegerAdd());
    }

    public static class IntegerAdd implements SampleConstraint
    {
        @Override
        public Constraint getConstraint()
        {
            final ConstraintBuilder builder = new ConstraintBuilder();

            builder.setName("Arithmetic");
            builder.setKind(ConstraintKind.FORMULA_BASED);
            builder.setDescription("Arithmetic constraint");

            final NodeVariable a = 
                new NodeVariable(builder.addVariable("a", DataType.INTEGER));

            final NodeValue value =
                new NodeValue(DataType.INTEGER.valueOf("-1487988057", 10));

            final NodeOperation sum =
                new NodeOperation(StandardOperation.ADD, value, value);

            builder.setInnerRep(new Formulas(new NodeOperation(StandardOperation.EQ, a, sum)));
            return builder.build();
        }

        @Override
        public Iterable<Variable> getExpectedVariables()
        {
            return Collections.singletonList(
                new Variable("a", DataType.INTEGER.valueOf("-2975976114", 10)));
        }
    }
}
