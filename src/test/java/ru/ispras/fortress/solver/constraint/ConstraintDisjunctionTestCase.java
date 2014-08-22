/*
 * Copyright (c) 2014 ISPRAS (www.ispras.ru)
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * ConstraintDisjunctionTestCase.java, Aug 22, 2014 7:41:12 PM Andrei Tatarnikov
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

import java.util.ArrayList;
import java.util.List;

import ru.ispras.fortress.data.Variable;

public class ConstraintDisjunctionTestCase extends GenericSolverTestBase
{
    public ConstraintDisjunctionTestCase()
    {
        super(new ConstraintDisjunction());
    }

    public static class ConstraintDisjunction extends BVUGTOperation
    {
        public Constraint getConstraint()
        {
            final Constraint constraint = super.getConstraint();
            final Constraint        neg = ConstraintCombiner.makeNegation(constraint);

            return ConstraintCombiner.makeDisjunction(constraint, neg);
        }

        @Override
        public Iterable<Variable> getExpectedVariables()
        {
            final List<Variable> result = new ArrayList<Variable>();

            result.add(new Variable("x", BIT_VECTOR_TYPE.valueOf("0", 10)));

            return result;
        }
    }
}
