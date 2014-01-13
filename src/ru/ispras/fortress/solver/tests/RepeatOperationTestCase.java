package ru.ispras.fortress.solver.tests;

import ru.ispras.fortress.solver.tests.common.GenericSolverSampleTestBase;
import ru.ispras.fortress.solver.tests.samples.ISampleConstraint;
import ru.ispras.fortress.solver.tests.samples.RepeatOperation;

public class RepeatOperationTestCase extends GenericSolverSampleTestBase
{

    @Override
    public ISampleConstraint createSample()
    {
        return new RepeatOperation();
    }

}
