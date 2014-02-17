package ru.ispras.fortress.solver;

import ru.ispras.fortress.solver.common.GenericSolverSampleTestBase;
import ru.ispras.fortress.solver.samples.Concatenation;
import ru.ispras.fortress.solver.samples.ISampleConstraint;

public class ConcatenationTestCase extends GenericSolverSampleTestBase
{
    @Override
    public ISampleConstraint createSample()
    {
        return new Concatenation();
    }
}
