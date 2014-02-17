package ru.ispras.fortress.solver.tests;

import ru.ispras.fortress.solver.tests.common.GenericSolverSampleTestBase;
import ru.ispras.fortress.solver.tests.samples.AbsCustomOperation;
import ru.ispras.fortress.solver.tests.samples.ISampleConstraint;

public class AbsCustomOperationTestCase extends GenericSolverSampleTestBase {

    @Override
    public ISampleConstraint createSample()
    {
        return new AbsCustomOperation();
    }
}
