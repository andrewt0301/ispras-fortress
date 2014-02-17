package ru.ispras.fortress.solver.tests;

import ru.ispras.fortress.solver.tests.common.GenericSolverSampleTestBase;
import ru.ispras.fortress.solver.tests.samples.ConstraintNegation;
import ru.ispras.fortress.solver.tests.samples.ISampleConstraint;

public class ConstraintNegationTestCase extends GenericSolverSampleTestBase
{
    @Override
    public ISampleConstraint createSample()
    {
        return new ConstraintNegation();
    }
}
