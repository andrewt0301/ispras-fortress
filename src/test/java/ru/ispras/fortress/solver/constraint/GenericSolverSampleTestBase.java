/*
 * Copyright (c) 2012 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * GenericSolverSampleTestBase.java, Oct 4, 2012 4:20:59 PM Andrei Tatarnikov
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

import org.junit.After;
import org.junit.Before;

import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.solver.constraint.Constraint;

public abstract class GenericSolverSampleTestBase extends GenericSolverTestBase
{
    private ISampleConstraint sample = null;

    public abstract ISampleConstraint createSample();

    @Before
    public void setUp()
    {
        sample = createSample();
    }

    public Constraint getConstraint()
    {
        return sample.getConstraint();
    }

    public Iterable<Variable> getExpectedVariables()
    {
        return sample.getExpectedVariables();
    }

    @After
    public void tearDown()
    {
        sample = null;
    }
}
