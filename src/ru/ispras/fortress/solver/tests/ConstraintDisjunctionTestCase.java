package ru.ispras.fortress.solver.tests;

import ru.ispras.fortress.solver.tests.common.GenericSolverSampleTestBase;
import ru.ispras.fortress.solver.tests.samples.ConstraintDisjunction;
import ru.ispras.fortress.solver.tests.samples.ISampleConstraint;

public class ConstraintDisjunctionTestCase extends GenericSolverSampleTestBase
{
    @Override
    public ISampleConstraint createSample()
    {
        return new ConstraintDisjunction();
    }
}
