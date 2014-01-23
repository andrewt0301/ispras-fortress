package ru.ispras.fortress.solver.tests.samples;

import java.util.ArrayList;
import java.util.List;


import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.*;
import ru.ispras.fortress.solver.Solver;
import ru.ispras.fortress.solver.SolverId;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintBuilder;
import ru.ispras.fortress.solver.constraint.ConstraintKind;
import ru.ispras.fortress.solver.constraint.Formulas;
import ru.ispras.fortress.solver.function.FunctionFactory;
import ru.ispras.fortress.solver.function.FunctionOperation;


/* The constraint as described in the SMT language:

(declare-const a Real)
(declare-const b Real)
(define-fun ABS ((x Real)) Real( ite( >= x  0.0) x( ~ x)))
(assert( =( ABS( ~  5.0))  5.0))
(assert( =( ABS  5.0)  5.0))
(assert( =( ABS( ~ a))  5.0))
(assert( =( ABS b)  5.0))
(check-sat)
(get-value ( a b))
(exit)

Expected output:
sat
((a (- 5.0))
 (b (- 5.0)))

*/
public class AbsCustomOperation implements ISampleConstraint
{
    private static final DataType realType = DataType.REAL;

    @Override
    public Constraint getConstraint()
    {
        final Solver solver = SolverId.Z3_TEXT.getSolver();
        assert solver != null;

        solver.addCustomOperation(
            FunctionOperation.ABS,
            FunctionFactory.makeAbs(new Variable("x", realType)));

        final ConstraintBuilder builder = new ConstraintBuilder();

        builder.setName("AbsCustomOperation");
        builder.setKind(ConstraintKind.FORMULA_BASED);
        builder.setDescription("AbsCustomOperation constraint");

        final NodeVariable a = new NodeVariable(builder.addVariable("a", realType));
        final NodeVariable b = new NodeVariable(builder.addVariable("b", realType));

        final Formulas formulas = new Formulas();
        builder.setInnerRep(formulas);

        formulas.add(
            new NodeExpr(
                StandardOperation.EQ,
                new NodeExpr(
                    FunctionOperation.ABS,
                    new NodeExpr(StandardOperation.MINUS, new NodeValue(realType.valueOf("5.0",10)))
                ),
                new NodeValue(realType.valueOf("5.0", 10))
            )
        );
        
        formulas.add(
            new NodeExpr(
                StandardOperation.EQ,
                new NodeExpr(
                    FunctionOperation.ABS,
                    new NodeValue(realType.valueOf("5.0",10))
                ),
                new NodeValue(realType.valueOf("5.0", 10))
            )
        );

        formulas.add(
            new NodeExpr(
                StandardOperation.EQ,
                new NodeExpr(
                    FunctionOperation.ABS,
                    new NodeExpr(StandardOperation.MINUS, a)
                ),
                new NodeValue(realType.valueOf("5.0",10))
            )
        );

        formulas.add(
            new NodeExpr(
                StandardOperation.EQ,
                new NodeExpr(FunctionOperation.ABS, b),
                new NodeValue(realType.valueOf("5.0",10))
            )
        );

        return builder.build();
    }

    @Override
    public Iterable<Variable> getExpectedVariables()
    {
        final List<Variable> result = new ArrayList<Variable>();

        result.add(new Variable("a", realType.valueOf("-5.0", 10)));
        result.add(new Variable("b", realType.valueOf("-5.0", 10)));

        return result;
    }

}
