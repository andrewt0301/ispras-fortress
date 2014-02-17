package ru.ispras.fortress.solver.tests.samples;

import java.util.ArrayList;
import java.util.List;


import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.*;
import ru.ispras.fortress.solver.Solver;
import ru.ispras.fortress.solver.SolverId;
import ru.ispras.fortress.solver.constraint.*;
import ru.ispras.fortress.solver.function.FunctionFactory;
import ru.ispras.fortress.solver.function.FunctionOperation;


/* The constraint as described in the SMT language:

(declare-const a Real)
(declare-const b Real)
(define-fun MAX ((x Real)(y Real)) Real( ite( >= x y) x y))
(assert( = a( MAX  3.0  4.0)))
(assert( = b( MAX a  5.0)))
(check-sat)
(get-value ( a b))
(exit)

Expected output:
sat
((a 4.0)
 (b 5.0))

*/
public class MaxCustomOperation implements ISampleConstraint
{
    private static final DataType realType = DataType.REAL;

    @Override
    public Constraint getConstraint()
    {
        final Solver solver = SolverId.Z3_TEXT.getSolver();
        assert solver != null;

        solver.addCustomOperation(
            FunctionOperation.MAX,
            FunctionFactory.makeMax(
                new Variable("x", realType),
                new Variable("y", realType)
            )
        );

        final ConstraintBuilder builder = new ConstraintBuilder();

        builder.setName("MaxCustomOperation");
        builder.setKind(ConstraintKind.FORMULA_BASED);
        builder.setDescription("MaxCustomOperation constraint");

        final NodeVariable a = new NodeVariable(builder.addVariable("a", realType));
        final NodeVariable b = new NodeVariable(builder.addVariable("b", realType));

        final Formulas formulas = new Formulas();
        builder.setInnerRep(formulas);

        formulas.add(
            new NodeExpr(
                StandardOperation.EQ,
                a,
                new NodeExpr(
                    FunctionOperation.MAX,
                    new NodeValue(realType.valueOf("3", 10)),
                    new NodeValue(realType.valueOf("4", 10)))));

        formulas.add(
            new NodeExpr(
                StandardOperation.EQ,
                b,
                new NodeExpr(
                    FunctionOperation.MAX,
                    a,
                    new NodeValue(realType.valueOf("5.0", 10)))));

        return builder.build();
    }

    @Override
    public Iterable<Variable> getExpectedVariables()
    {
        final List<Variable> result = new ArrayList<Variable>();

        result.add(new Variable("a", realType.valueOf("4.0", 10)));
        result.add(new Variable("b", realType.valueOf("5.0", 10)));

        return result;
    }

}
