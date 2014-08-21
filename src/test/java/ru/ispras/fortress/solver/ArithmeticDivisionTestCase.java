package ru.ispras.fortress.solver;

import java.util.ArrayList;
import java.util.List;

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintBuilder;
import ru.ispras.fortress.solver.constraint.ConstraintKind;
import ru.ispras.fortress.solver.constraint.Formulas;

public class ArithmeticDivisionTestCase extends GenericSolverSampleTestBase
{
    @Override
    public ISampleConstraint createSample()
    {
        return new ArithmeticDivision();
    }

    /** The constraint as described in the SMT language:

    <pre>
    (declare-const a Int)
    (declare-const r1 Int)
    (declare-const r2 Int)
    (declare-const r3 Int)
    (declare-const r4 Int)
    (declare-const r5 Int)
    (declare-const r6 Int)
    (assert (= a 10))
    (assert (= r1 (div a 4)))
    (assert (= r2 (mod a 4)))
    (assert (= r3 (rem a 4)))
    (assert (= r4 (div a (- 4))))
    (assert (= r5 (mod a (- 4))))
    (assert (= r6 (rem a (- 4))))
    (check-sat)
    (get-value (a r1 r2 r3 r4 r5 r6))
    (exit)</pre>

    Expected output:
    sat
    ((a 10)
     (r1 2)
     (r2 2)
     (r3 2)
     (r4 (- 2))
     (r5 2)
     (r6 (- 2)))
    */

    public static class ArithmeticDivision implements ISampleConstraint
    {
        private static final DataType intType = DataType.INTEGER;

        @Override
        public Constraint getConstraint()
        {
            final ConstraintBuilder builder = new ConstraintBuilder();

            builder.setName("ArithmeticDivision");
            builder.setDescription("ArithmeticDivision constraint");
            builder.setKind(ConstraintKind.FORMULA_BASED);

            final NodeVariable a  = new NodeVariable(builder.addVariable("a", intType));
            final NodeVariable r1 = new NodeVariable(builder.addVariable("r1", intType));
            final NodeVariable r2 = new NodeVariable(builder.addVariable("r2", intType));
            final NodeVariable r3 = new NodeVariable(builder.addVariable("r3", intType));
            final NodeVariable r4 = new NodeVariable(builder.addVariable("r4", intType));
            final NodeVariable r5 = new NodeVariable(builder.addVariable("r5", intType));
            final NodeVariable r6 = new NodeVariable(builder.addVariable("r6", intType));

            final Formulas formulas = new Formulas();
            builder.setInnerRep(formulas);

            formulas.add(
                new NodeOperation(
                    StandardOperation.EQ,
                    a,
                    new NodeValue(intType.valueOf("10", 10))));

            formulas.add(
                new NodeOperation(
                    StandardOperation.EQ,
                    r1,
                    new NodeOperation(
                        StandardOperation.DIV,
                        a,
                        new NodeValue(intType.valueOf("4", 10)))));

            formulas.add(
                new NodeOperation(
                    StandardOperation.EQ,
                    r2,
                    new NodeOperation(
                        StandardOperation.MOD,
                        a,
                        new NodeValue(intType.valueOf("4", 10)))));

            formulas.add(
                new NodeOperation(
                    StandardOperation.EQ,
                    r3,
                    new NodeOperation(
                        StandardOperation.REM,
                        a,
                        new NodeValue(intType.valueOf("4", 10)))));
            
            formulas.add(
                new NodeOperation(
                    StandardOperation.EQ,
                    r4,
                    new NodeOperation(
                        StandardOperation.DIV,
                        a,
                        new NodeValue(intType.valueOf("-4", 10)))));

            formulas.add(
                new NodeOperation(
                    StandardOperation.EQ,
                    r5,
                    new NodeOperation(
                        StandardOperation.MOD,
                        a,
                        new NodeValue(intType.valueOf("-4", 10)))));

            formulas.add(
                new NodeOperation(
                    StandardOperation.EQ,
                    r6,
                    new NodeOperation(
                        StandardOperation.REM,
                        a,
                        new NodeValue(intType.valueOf("-4", 10)))));

            return builder.build();
        }

        @Override
        public Iterable<Variable> getExpectedVariables()
        {
            final List<Variable> result = new ArrayList<Variable>();

            result.add(new Variable("a", intType.valueOf("10", 10)));
            result.add(new Variable("r1", intType.valueOf("2", 10)));
            result.add(new Variable("r2", intType.valueOf("2", 10)));
            result.add(new Variable("r3", intType.valueOf("2", 10)));
            result.add(new Variable("r4", intType.valueOf("-2", 10)));
            result.add(new Variable("r5", intType.valueOf("2", 10)));
            result.add(new Variable("r6", intType.valueOf("-2", 10)));

            return result;
        }
    }
}
