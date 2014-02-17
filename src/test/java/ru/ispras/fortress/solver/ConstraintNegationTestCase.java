package ru.ispras.fortress.solver;

import ru.ispras.fortress.solver.common.GenericSolverSampleTestBase;
import ru.ispras.fortress.solver.samples.ConstraintNegation;
import ru.ispras.fortress.solver.samples.ISampleConstraint;

public class ConstraintNegationTestCase extends GenericSolverSampleTestBase
{
    @Override
    public ISampleConstraint createSample()
    {
        return new ConstraintNegation();
    }
}
