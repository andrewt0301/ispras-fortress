package ru.ispras.fortress.solver;

import ru.ispras.fortress.solver.common.GenericSolverSampleTestBase;
import ru.ispras.fortress.solver.samples.Arithmetic;
import ru.ispras.fortress.solver.samples.ISampleConstraint;

public class ArithmeticTestCase extends GenericSolverSampleTestBase
{
    @Override
    public ISampleConstraint createSample()
    {
        return new Arithmetic();
    }
}
