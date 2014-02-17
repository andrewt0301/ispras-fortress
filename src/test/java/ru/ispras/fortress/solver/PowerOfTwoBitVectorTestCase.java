/*
 * Copyright (c) 2012 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * PowerOfTwoBitVectorTestCase.java, Jan 13, 2012 2:27:33 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver;

import ru.ispras.fortress.solver.common.GenericSolverSampleTestBase;
import ru.ispras.fortress.solver.samples.PowerOfTwo;

public class PowerOfTwoBitVectorTestCase extends GenericSolverSampleTestBase
{
    @Override
    public PowerOfTwo createSample()
    {
        return new PowerOfTwo();
    }
}
