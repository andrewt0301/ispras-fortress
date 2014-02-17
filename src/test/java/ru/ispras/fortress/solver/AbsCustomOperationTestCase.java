package ru.ispras.fortress.solver;

import ru.ispras.fortress.solver.common.GenericSolverSampleTestBase;
import ru.ispras.fortress.solver.samples.AbsCustomOperation;
import ru.ispras.fortress.solver.samples.ISampleConstraint;

public class AbsCustomOperationTestCase extends GenericSolverSampleTestBase
{
    @Override
    public ISampleConstraint createSample()
    {
        return new AbsCustomOperation();
    }
}
