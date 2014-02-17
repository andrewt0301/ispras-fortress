package ru.ispras.fortress.solver;

import ru.ispras.fortress.solver.common.GenericSolverSampleTestBase;
import ru.ispras.fortress.solver.samples.ConstraintDisjunction;
import ru.ispras.fortress.solver.samples.ISampleConstraint;

public class ConstraintDisjunctionTestCase extends GenericSolverSampleTestBase
{
    @Override
    public ISampleConstraint createSample()
    {
        return new ConstraintDisjunction();
    }
}
