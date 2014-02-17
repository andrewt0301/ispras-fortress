package ru.ispras.fortress.solver;

import ru.ispras.fortress.solver.common.GenericSolverSampleTestBase;
import ru.ispras.fortress.solver.samples.ArithmeticDivision;
import ru.ispras.fortress.solver.samples.ISampleConstraint;

public class ArithmeticDivisionTestCase extends GenericSolverSampleTestBase
{
    @Override
    public ISampleConstraint createSample()
    {
        return new ArithmeticDivision();
    }
}
