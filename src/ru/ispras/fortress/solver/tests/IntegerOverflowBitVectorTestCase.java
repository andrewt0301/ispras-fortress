/*
 * Copyright (c) 2012 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * IntegerOverflowBitVectorTestCase.java, Jan 13, 2012 2:44:00 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver.tests;

import ru.ispras.fortress.solver.tests.common.GenericSolverSampleTestBase;
import ru.ispras.fortress.solver.tests.samples.IntegerOverflow;

public class IntegerOverflowBitVectorTestCase extends GenericSolverSampleTestBase
{
    @Override
    public IntegerOverflow createSample()
    {
        return new IntegerOverflow();
    }
}