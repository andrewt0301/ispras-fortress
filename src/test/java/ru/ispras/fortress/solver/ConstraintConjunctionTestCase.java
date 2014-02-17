package ru.ispras.fortress.solver;

import ru.ispras.fortress.solver.common.GenericSolverSampleTestBase;
import ru.ispras.fortress.solver.samples.ConstraintConjunction;
import ru.ispras.fortress.solver.samples.ISampleConstraint;

public class ConstraintConjunctionTestCase extends GenericSolverSampleTestBase
{
    @Override
    public ISampleConstraint createSample()
    {
        return new ConstraintConjunction();
    }
}
