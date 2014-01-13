package ru.ispras.fortress.solver.tests;

import ru.ispras.fortress.solver.tests.common.GenericSolverSampleTestBase;
import ru.ispras.fortress.solver.tests.samples.ConstraintConjunction;
import ru.ispras.fortress.solver.tests.samples.ISampleConstraint;

public class ConstraintConjunctionTestCase extends GenericSolverSampleTestBase
{
    @Override
    public ISampleConstraint createSample()
    {
        return new ConstraintConjunction();
    }
}
