/*
 * Copyright (c) 2012 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * CustomOperationsTestCase.java, Oct 4, 2012 12:15:18 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver.tests;

import ru.ispras.fortress.solver.tests.common.GenericSolverSampleTestBase;
import ru.ispras.fortress.solver.tests.samples.CustomOperations;

public class CustomOperationsTestCase extends GenericSolverSampleTestBase
{
    @Override
    public CustomOperations createSample()
    {
        return new CustomOperations();
    }
}
