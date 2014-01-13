/*
 * Copyright (c) 2012 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * PowerOfTwoCustomTestCase.java, Oct 5, 2012 3:29:51 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver.tests;

import ru.ispras.fortress.solver.tests.common.GenericSolverSampleTestBase;
import ru.ispras.fortress.solver.tests.samples.PowerOfTwoCustom;

public class PowerOfTwoCustomTestCase extends GenericSolverSampleTestBase
{
    @Override
    public PowerOfTwoCustom createSample()
    {
        return new PowerOfTwoCustom();
    }
}
