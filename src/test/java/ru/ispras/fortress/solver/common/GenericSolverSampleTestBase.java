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
 */

package ru.ispras.fortress.solver.common;

import org.junit.After;
import org.junit.Before;

import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.samples.ISampleConstraint;

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
