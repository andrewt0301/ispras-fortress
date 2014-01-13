/*
 * Copyright (c) 2012 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * InputParametersTestCase.java, Oct 4, 2012 11:29:56 AM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver.tests;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.tests.common.GenericSolverSampleTestBase;
import ru.ispras.fortress.solver.tests.samples.InputParameters;

public class InputParametersTestCase extends GenericSolverSampleTestBase
{
    @Override
    public Constraint getConstraint()
    {
        final Constraint constraint = super.getConstraint();

        constraint.setVariableValue("b", Data.createBitVector(2, 16));
        constraint.setVariableValue("c", Data.createBitVector(5, 16));

        return constraint;
    }

    @Override
    public InputParameters createSample()
    {
        return new InputParameters();
    }
}

