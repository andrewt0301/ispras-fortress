/*
 * Copyright (c) 2013 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * $Id: StandardCalculator.java, Jul 2, 2013 4:49:23 PM Andrei Tatarnikov Exp $
 */

package ru.ispras.fortress.solver.tests.samples;

import java.util.ArrayList;
import java.util.List;



import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.*;
import ru.ispras.fortress.solver.constraint.*;
import ru.ispras.fortress.transform.ReduceOptions;
import ru.ispras.fortress.transform.Transform;

/* The constraint as described in the SMT language:

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Int)
(declare-const e Int)
(declare-const f Int)

(assert (= a (+ 2 3)))
(assert (= b (- 10 6)))
(assert (= c (* 2 5)))
(assert (= d (div 12 5)))
(assert (= e (rem 10 3)))
(assert (= f (mod 10 3)))

(check-sat)
(get-value (a b c d e f))

Expected output:

sat ((a 5) (b 4) (c 10) (d 2) (e 1) (f 1))
*/

public class StandardCalculator implements ISampleConstraint
{
    private static final DataType intType = DataType.INTEGER;

    @Override
    public Constraint getConstraint()
    {
        final ConstraintBuilder builder = new ConstraintBuilder();

        builder.setName("StandardCalculator");
        builder.setKind(ConstraintKind.FORMULA_BASED);
        builder.setDescription("Expression reduction with the standard expression calculator.");

        final NodeVariable a = new NodeVariable(builder.addVariable("a", intType));
        final NodeVariable b = new NodeVariable(builder.addVariable("b", intType));
        final NodeVariable c = new NodeVariable(builder.addVariable("c", intType));
        final NodeVariable d = new NodeVariable(builder.addVariable("d", intType));
        final NodeVariable e = new NodeVariable(builder.addVariable("e", intType));
        final NodeVariable f = new NodeVariable(builder.addVariable("f", intType));

        final Formulas formulas = new Formulas();
        builder.setInnerRep(formulas);

        formulas.add(
            new NodeExpr(
                StandardOperation.EQ,
                a,
                Transform.reduce(
                    ReduceOptions.NEW_INSTANCE,
                    new NodeExpr(
                        StandardOperation.ADD,
                        new NodeValue(intType.valueOf("2", 10)),
                        new NodeValue(intType.valueOf("3", 10))
                    )
                )
            )
        );

        formulas.add(
            new NodeExpr(
                StandardOperation.EQ,
                b, 
                Transform.reduce(
                    ReduceOptions.NEW_INSTANCE,
                    new NodeExpr(
                        StandardOperation.SUB,
                        new NodeValue(intType.valueOf("10", 10)),
                        new NodeValue(intType.valueOf("6", 10))
                    )
                )
            )
        );

        formulas.add(
            new NodeExpr(
                StandardOperation.EQ,
                c, 
                Transform.reduce(
                    ReduceOptions.NEW_INSTANCE,
                    new NodeExpr(
                        StandardOperation.MUL,
                        new NodeValue(intType.valueOf("2", 10)),
                        new NodeValue(intType.valueOf("5", 10))
                    )
                )
            )
        );

        formulas.add(
            new NodeExpr(
                StandardOperation.EQ,
                d,
                Transform.reduce(
                    ReduceOptions.NEW_INSTANCE,
                    new NodeExpr(
                        StandardOperation.DIV,
                        new NodeValue(intType.valueOf("12", 10)),
                        new NodeValue(intType.valueOf("5", 10))
                    )
                )
            )
        );

        formulas.add(
            new NodeExpr(
                StandardOperation.EQ,
                e,
                Transform.reduce(
                    ReduceOptions.NEW_INSTANCE,
                    new NodeExpr(
                        StandardOperation.REM,
                        new NodeValue(intType.valueOf("10", 10)),
                        new NodeValue(intType.valueOf("3", 10))
                    )
                )
            )
        );

        formulas.add(
            new NodeExpr(
                StandardOperation.EQ,
                f,
                Transform.reduce(
                    ReduceOptions.NEW_INSTANCE,
                    new NodeExpr(
                        StandardOperation.MOD,
                        new NodeValue(intType.valueOf("10", 10)),
                        new NodeValue(intType.valueOf("3", 10))
                    )
                )
            )
        );

        return builder.build();
    }

    @Override
    public Iterable<Variable> getExpectedVariables()
    {
        final List<Variable> result = new ArrayList<Variable>();

        result.add(new Variable("a", intType.valueOf("5", 10)));
        result.add(new Variable("b", intType.valueOf("4", 10)));
        result.add(new Variable("c", intType.valueOf("10", 10)));
        result.add(new Variable("d", intType.valueOf("2", 10)));
        result.add(new Variable("e", intType.valueOf("1", 10)));
        result.add(new Variable("f", intType.valueOf("1", 10)));
        
        return result;
    }
}
