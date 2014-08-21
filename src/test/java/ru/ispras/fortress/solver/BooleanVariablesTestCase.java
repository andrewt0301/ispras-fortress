/*
 * Copyright (c) 2014 ISPRAS (www.ispras.ru)
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * BooleanVariablesTestCase.java, Jul 28, 2014 4:18:30 PM Andrei Tatarnikov
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

package ru.ispras.fortress.solver;

import java.util.ArrayList;
import java.util.List;

import ru.ispras.fortress.data.Data;
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

/*

(declare-const x Bool)
(declare-const y Bool)
(assert (= x true))
(assert (= y false))
(check-sat)
(get-value (x y))
(exit)

sat
((x true)
 (y false))

*/

public class BooleanVariablesTestCase extends GenericSolverSampleTestBase
{
    @Override
    public ISampleConstraint createSample()
    {
        return new BooleanVariables();
    }

    public static class BooleanVariables implements ISampleConstraint
    {
        @Override
        public Constraint getConstraint()
        {
            final ConstraintBuilder builder = new ConstraintBuilder();

            builder.setName("BooleanVariables");
            builder.setKind(ConstraintKind.FORMULA_BASED);
            builder.setDescription("A constaint with boolean variables");

            final NodeVariable x = new NodeVariable(
                builder.addVariable("x", DataType.BOOLEAN));

            final NodeVariable y = new NodeVariable(
                builder.addVariable("y", DataType.BOOLEAN));

            final Formulas formulas = new Formulas();
            builder.setInnerRep(formulas);

            formulas.add(
                new NodeOperation(
                    StandardOperation.EQ, x, NodeValue.newBoolean(true))
            );

            formulas.add(
                new NodeOperation(
                    StandardOperation.EQ, y, NodeValue.newBoolean(false))
            );

            return builder.build();
        }

        @Override
        public Iterable<Variable> getExpectedVariables()
        {
            final List<Variable> result = new ArrayList<Variable>();

            result.add(new Variable("x", Data.newBoolean(true)));
            result.add(new Variable("y", Data.newBoolean(false)));

            return result;
        }
    }
}
