package ru.ispras.fortress.solver.tests;

import ru.ispras.fortress.solver.tests.common.GenericSolverSampleTestBase;
import ru.ispras.fortress.solver.tests.samples.ArithmeticDivision;
import ru.ispras.fortress.solver.tests.samples.ISampleConstraint;

public class ArithmeticDivisionTestCase extends GenericSolverSampleTestBase
{

    @Override
    public ISampleConstraint createSample()
    {
        return new ArithmeticDivision();
    }
}
