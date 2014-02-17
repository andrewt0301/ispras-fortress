/*
 * Copyright (c) 2013 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * StandardCalculatorTestCase.java, Jul 2, 2013 5:42:36 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver.tests;

import ru.ispras.fortress.solver.tests.common.GenericSolverSampleTestBase;
import ru.ispras.fortress.solver.tests.samples.ISampleConstraint;
import ru.ispras.fortress.solver.tests.samples.StandardCalculator;

public class StandardCalculatorTestCase extends GenericSolverSampleTestBase
{
    @Override
    public ISampleConstraint createSample()
    {
        return new StandardCalculator();
    }
}
