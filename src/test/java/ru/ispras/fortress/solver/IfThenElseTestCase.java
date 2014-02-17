package ru.ispras.fortress.solver;

import ru.ispras.fortress.solver.common.GenericSolverSampleTestBase;
import ru.ispras.fortress.solver.samples.ISampleConstraint;
import ru.ispras.fortress.solver.samples.IfThenElse;

public class IfThenElseTestCase extends GenericSolverSampleTestBase
{
    @Override
    public ISampleConstraint createSample()
    {
        return new IfThenElse();
    }
}
