/*
 * Copyright (c) 2012 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * SimpleBitVectorTestCase.java, Jan 13, 2012 2:10:58 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver;

import ru.ispras.fortress.solver.common.GenericSolverSampleTestBase;
import ru.ispras.fortress.solver.samples.SimpleBitVector;

public class SimpleBitVectorTestCase extends GenericSolverSampleTestBase
{
    @Override
    public SimpleBitVector createSample()
    {
        return new SimpleBitVector();
    }
}
