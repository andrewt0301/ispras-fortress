package ru.ispras.fortress.solver.tests;

import ru.ispras.fortress.solver.tests.common.GenericSolverSampleTestBase;
import ru.ispras.fortress.solver.tests.samples.ISampleConstraint;
import ru.ispras.fortress.solver.tests.samples.ReductionCustomOperations;

public class ReductionCustomOperationsTestCase extends GenericSolverSampleTestBase
{
    @Override
    public ISampleConstraint createSample()
    {
        return new ReductionCustomOperations();
    }
}
