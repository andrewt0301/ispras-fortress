package ru.ispras.fortress.solver.tests;

import ru.ispras.fortress.solver.tests.common.GenericSolverSampleTestBase;
import ru.ispras.fortress.solver.tests.samples.ISampleConstraint;
import ru.ispras.fortress.solver.tests.samples.UnaryOperations;

public class UnaryOperationsTestCase extends GenericSolverSampleTestBase
{
    @Override
    public ISampleConstraint createSample()
    {
        return new UnaryOperations();
    }

}
