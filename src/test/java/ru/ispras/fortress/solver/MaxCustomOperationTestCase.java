package ru.ispras.fortress.solver;

import ru.ispras.fortress.solver.common.GenericSolverSampleTestBase;
import ru.ispras.fortress.solver.samples.ISampleConstraint;
import ru.ispras.fortress.solver.samples.MaxCustomOperation;

public class MaxCustomOperationTestCase extends GenericSolverSampleTestBase 
{
    @Override
    public ISampleConstraint createSample()
    {
        return new MaxCustomOperation();
    }
}
