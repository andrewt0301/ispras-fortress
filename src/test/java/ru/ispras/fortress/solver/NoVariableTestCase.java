/*
 * Copyright (c) 2014 ISPRAS (www.ispras.ru)
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * NoVariableTestCase.java, Jul 28, 2014 2:28:51 PM Andrei Tatarnikov
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

import java.util.Collections;

import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintBuilder;
import ru.ispras.fortress.solver.constraint.ConstraintKind;
import ru.ispras.fortress.solver.constraint.Formulas;

public class NoVariableTestCase extends GenericSolverSampleTestBase
{

    /** The constraint as described in the SMT language:

     <pre>
     (assert true)
     (check-sat)
     (exit)</pre>

     Expected output:

     <pre>
     sat</pre>
     */

    @Override
    public ISampleConstraint createSample()
    { 
        return new NoVariable();
    }

    public static class NoVariable implements ISampleConstraint
    {
        @Override 
        public Constraint getConstraint()
        {
            final ConstraintBuilder builder = new ConstraintBuilder();

            builder.setName("NoVariable");
            builder.setKind(ConstraintKind.FORMULA_BASED);
            builder.setDescription("NoVariable constraint");

            final Formulas formulas = new Formulas(NodeValue.newBoolean(true));
            builder.setInnerRep(formulas);

            return builder.build();
        }

        @Override
        public Iterable<Variable> getExpectedVariables()
        { 
            return Collections.emptyList();
        }
    }
}
