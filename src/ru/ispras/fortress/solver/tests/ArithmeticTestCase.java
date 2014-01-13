package ru.ispras.fortress.solver.tests;

import ru.ispras.fortress.solver.tests.common.GenericSolverSampleTestBase;
import ru.ispras.fortress.solver.tests.samples.Arithmetic;
import ru.ispras.fortress.solver.tests.samples.ISampleConstraint;

public class ArithmeticTestCase extends GenericSolverSampleTestBase
{

    @Override
    public ISampleConstraint createSample()
    {
        return new Arithmetic();
    }
}
