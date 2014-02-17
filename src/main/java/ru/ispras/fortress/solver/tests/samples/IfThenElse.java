package ru.ispras.fortress.solver.tests.samples;

import java.util.ArrayList;
import java.util.List;


import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.*;
import ru.ispras.fortress.solver.constraint.*;

/* The constraint as described in the SMT language:

(declare-const a Int)
(declare-const b Int)
(assert (> a 5))
(assert (< b 7))
(assert (= (ite (= a b) 1 0) 1))
(check-sat)
(get-value (a b))
(exit)

Expected output:
sat
((a 6)
 (b 6))

*/
public class IfThenElse implements ISampleConstraint
{
    private static final DataType intType = DataType.INTEGER;

    @Override
    public Constraint getConstraint()
    {
        final ConstraintBuilder builder = new ConstraintBuilder();

        builder.setName("IfThenElse");
        builder.setKind(ConstraintKind.FORMULA_BASED);
        builder.setDescription("IfThenElse constraint");

        final NodeVariable a = new NodeVariable(builder.addVariable("a", intType));
        final NodeVariable b = new NodeVariable(builder.addVariable("b", intType));

        final Formulas formulas = new Formulas();
        builder.setInnerRep(formulas);

        formulas.add(
            new NodeExpr(
                StandardOperation.GREATER,
                a,
                new NodeValue(intType.valueOf("5", 10))
            )
        );

        formulas.add(
            new NodeExpr(
                StandardOperation.LESS,
                b,
                new NodeValue(intType.valueOf("7", 10))
            )
        );

        formulas.add(
            new NodeExpr(
                StandardOperation.EQ,
                new NodeExpr(
                    StandardOperation.ITE,
                    new NodeExpr(StandardOperation.EQ, a, b),
                    new NodeValue(intType.valueOf("1", 10)),
                    new NodeValue(intType.valueOf("0", 10))
                ),
                new NodeValue(intType.valueOf("1", 10))
            )
        );

        return builder.build();
    }

    @Override
    public Iterable<Variable> getExpectedVariables()
    {
        final List<Variable> result = new ArrayList<Variable>();

        result.add(new Variable("a", intType.valueOf("6", 10)));
        result.add(new Variable("b", intType.valueOf("6", 10)));

        return result;
    }
}
