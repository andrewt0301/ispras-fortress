package ru.ispras.fortress.solver;

import java.util.ArrayList;
import java.util.List;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.NodeExpr;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintBuilder;
import ru.ispras.fortress.solver.constraint.ConstraintKind;
import ru.ispras.fortress.solver.constraint.Formulas;

public class MaxCustomOperationTestCase extends GenericSolverSampleTestBase 
{
    @Override
    public ISampleConstraint createSample()
    {
        return new MaxCustomOperation();
    }

    /** The constraint as described in the SMT language:

    <pre>
    (declare-const a Real)
    (declare-const b Real)
    (define-fun MAX ((x Real)(y Real)) Real( ite( >= x y) x y))
    (assert( = a( MAX  3.0  4.0)))
    (assert( = b( MAX a  5.0)))
    (check-sat)
    (get-value ( a b))
    (exit)</pre>

    Expected output:

    <pre>
    sat ((a 4.0)(b 5.0))</pre>    
    */

    public static class MaxCustomOperation implements ISampleConstraint
    {
        @Override
        public Constraint getConstraint()
        {
            final ConstraintBuilder builder = new ConstraintBuilder();

            builder.setName("MaxCustomOperation");
            builder.setKind(ConstraintKind.FORMULA_BASED);
            builder.setDescription("MaxCustomOperation constraint");

            final NodeVariable a = new NodeVariable(builder.addVariable("a", DataType.REAL));
            final NodeVariable b = new NodeVariable(builder.addVariable("b", DataType.REAL));
            final NodeVariable c = new NodeVariable(builder.addVariable("c", DataType.INTEGER));
            final NodeVariable d = new NodeVariable(builder.addVariable("d", DataType.INTEGER));

            final Formulas formulas = new Formulas();
            builder.setInnerRep(formulas);

            formulas.add(
                new NodeExpr(
                    StandardOperation.EQ,
                    a,
                    new NodeExpr(
                        StandardOperation.MAX,
                        NodeValue.newReal(3),
                        NodeValue.newReal(4))));

            formulas.add(
                new NodeExpr(
                    StandardOperation.EQ,
                    b,
                    new NodeExpr(
                        StandardOperation.MAX,
                        a,
                        NodeValue.newReal(5))));
            
            formulas.add(
                new NodeExpr(
                    StandardOperation.EQ,
                    c,
                    new NodeExpr(
                        StandardOperation.MAX,
                        NodeValue.newInteger(3),
                        NodeValue.newInteger(4))));

            formulas.add(
                new NodeExpr(
                    StandardOperation.EQ,
                    d,
                    new NodeExpr(
                        StandardOperation.MAX,
                        c,
                        NodeValue.newInteger(5))));

            return builder.build();
        }

        @Override
        public Iterable<Variable> getExpectedVariables()
        {
            final List<Variable> result = new ArrayList<Variable>();

            result.add(new Variable("a", Data.newReal(4.0)));
            result.add(new Variable("b", Data.newReal(5.0)));
            result.add(new Variable("c", Data.newInteger(4)));
            result.add(new Variable("d", Data.newInteger(5)));

            return result;
        }
    }
}
