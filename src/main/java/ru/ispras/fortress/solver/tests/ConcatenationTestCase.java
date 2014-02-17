package ru.ispras.fortress.solver.tests;

import ru.ispras.fortress.solver.tests.common.GenericSolverSampleTestBase;
import ru.ispras.fortress.solver.tests.samples.Concatenation;
import ru.ispras.fortress.solver.tests.samples.ISampleConstraint;

public class ConcatenationTestCase extends GenericSolverSampleTestBase
{

    @Override
    public ISampleConstraint createSample()
    {
        return new Concatenation();
    }
}
