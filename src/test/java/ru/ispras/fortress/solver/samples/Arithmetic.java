package ru.ispras.fortress.solver.samples;

import java.util.ArrayList;
import java.util.List;


import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.*;
import ru.ispras.fortress.solver.constraint.*;

/* The constraint as described in the SMT language:

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Real)
(declare-const e Real)
(assert (> a (+ b 2)))
(assert (= a (+ (* 2 c) 10)))
(assert (<= (+ c b) 1000))
(assert (>= d e))
(check-sat)
(get-value (a b c d e))
(exit)

Expected output:
sat
((a 0)
 (b (- 3))
 (c (- 5))
 (d 0.0)
 (e 0.0))

*/

public class Arithmetic implements ISampleConstraint
{
    private static final DataType intType  = DataType.INTEGER;
    private static final DataType realType = DataType.REAL;

    @Override
    public Constraint getConstraint()
    {
        final ConstraintBuilder builder = new ConstraintBuilder();

        builder.setName("Arithmetic");
        builder.setKind(ConstraintKind.FORMULA_BASED);
        builder.setDescription("Arithmetic constraint");

        final NodeVariable a = new NodeVariable(builder.addVariable("a", intType));
        final NodeVariable b = new NodeVariable(builder.addVariable("b", intType));
        final NodeVariable c = new NodeVariable(builder.addVariable("c", intType));
        final NodeVariable d = new NodeVariable(builder.addVariable("d", realType));
        final NodeVariable e = new NodeVariable(builder.addVariable("e", realType));

        final Formulas formulas = new Formulas();
        builder.setInnerRep(formulas);

        formulas.add(
            new NodeExpr(
                StandardOperation.GREATER,
                a, 
                new NodeExpr(StandardOperation.ADD, b, new NodeValue(intType.valueOf("2", 10)))
            )
        );

        formulas.add(
            new NodeExpr(
                StandardOperation.EQ, 
                a, 
                new NodeExpr(
                    StandardOperation.ADD, 
                    new NodeExpr(StandardOperation.MUL, new NodeValue(intType.valueOf("2", 10)), c),
                    new NodeValue(intType.valueOf("10", 10))
                )
            )
        );

        formulas.add(
            new NodeExpr(
                StandardOperation.LESSEQ,
                new NodeExpr(StandardOperation.ADD, c, b),
                new NodeValue(intType.valueOf("1000", 10))
            )
        );

        formulas.add(
            new NodeExpr(StandardOperation.GREATEREQ, d, e)
        );

        return builder.build();
    }

    @Override
    public Iterable<Variable> getExpectedVariables()
    {
        final List<Variable> result = new ArrayList<Variable>();

        result.add(new Variable("a", intType.valueOf("0", 10)));
        result.add(new Variable("b", intType.valueOf("-3", 10)));
        result.add(new Variable("c", intType.valueOf("-5", 10)));
        result.add(new Variable("d", realType.valueOf("0.0", 10)));
        result.add(new Variable("e", realType.valueOf("0.0", 10)));

        return result;
    }
}
