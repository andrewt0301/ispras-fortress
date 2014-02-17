package ru.ispras.fortress.solver;

import java.util.ArrayList;
import java.util.List;

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.NodeExpr;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.solver.common.GenericSolverSampleTestBase;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintBuilder;
import ru.ispras.fortress.solver.constraint.ConstraintKind;
import ru.ispras.fortress.solver.constraint.Formulas;
import ru.ispras.fortress.solver.function.FunctionFactory;
import ru.ispras.fortress.solver.function.FunctionOperation;
import ru.ispras.fortress.solver.samples.ISampleConstraint;

public class MinCustomOperationTestCase extends GenericSolverSampleTestBase
{
    @Override
    public ISampleConstraint createSample()
    {
        return new MinCustomOperation();
    }

    /** The constraint as described in the SMT language:

    <pre>
    (declare-const a Real)
    (declare-const b Real)
    (define-fun MIN ((x Real)(y Real)) Real( ite( >= x y) y x))
    (assert( = a( MIN  3.0  4.0)))
    (assert( = b( MIN a  2.0)))
    (check-sat)
    (get-value ( a b))
    (exit)</pre>

    Expected output:
   
    <pre>
    sat ((a 3.0)(b 2.0))</pre>
    */

    public static class MinCustomOperation implements ISampleConstraint
    {
        private static final DataType realType = DataType.REAL;

        @Override
        public Constraint getConstraint()
        {
            final Solver solver = SolverId.Z3_TEXT.getSolver();
            assert solver != null;

            solver.addCustomOperation(
                FunctionOperation.MIN,
                FunctionFactory.makeMin(
                    new Variable("x", realType),
                    new Variable("y", realType)
                )
            );

            final ConstraintBuilder builder = new ConstraintBuilder();

            builder.setName("MinCustomOperation");
            builder.setKind(ConstraintKind.FORMULA_BASED);
            builder.setDescription("MinCustomOperation constraint");

            final NodeVariable a = new NodeVariable(builder.addVariable("a", realType));
            final NodeVariable b = new NodeVariable(builder.addVariable("b", realType));

            final Formulas formulas = new Formulas();
            builder.setInnerRep(formulas);

            formulas.add(
                new NodeExpr(
                    StandardOperation.EQ,
                    a,
                    new NodeExpr(
                        FunctionOperation.MIN,
                        new NodeValue(realType.valueOf("3.0", 10)),
                        new NodeValue(realType.valueOf("4.0", 10)))));

            formulas.add(
                new NodeExpr(
                    StandardOperation.EQ,
                    b,
                    new NodeExpr(
                        FunctionOperation.MIN,
                        a,
                        new NodeValue(realType.valueOf("2.0", 10)))));

            return builder.build();
        }

        @Override
        public Iterable<Variable> getExpectedVariables()
        {
            final List<Variable> result = new ArrayList<Variable>();

            result.add(new Variable("a", realType.valueOf("3.0", 10)));
            result.add(new Variable("b", realType.valueOf("2.0", 10)));

            return result;
        }
    }
}
