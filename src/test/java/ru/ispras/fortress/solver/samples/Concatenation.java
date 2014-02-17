package ru.ispras.fortress.solver.samples;

import java.util.ArrayList;
import java.util.List;


import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.*;
import ru.ispras.fortress.solver.constraint.*;

/* The constraint as described in the SMT language:

(declare-const x (_ BitVec 16))
(declare-const y (_ BitVec 16))
(declare-const z (_ BitVec 32))
(assert (= x #x0000))
(assert (= y #xffff))
(assert (= z (concat x y)))
(check-sat)
(get-value (x y z))
(exit)

Expected output:
sat
((z #x0000ffff))

*/

public class Concatenation implements ISampleConstraint
{
    private static final int      BIT_VECTOR_ARG_SIZE = 16;
    private static final DataType BIT_VECTOR_ARG_TYPE = DataType.BIT_VECTOR(BIT_VECTOR_ARG_SIZE);
    private static final int      BIT_VECTOR_RES_SIZE = 32;
    private static final DataType BIT_VECTOR_RES_TYPE = DataType.BIT_VECTOR(BIT_VECTOR_RES_SIZE);

    private static final int HEX_RADIX = 16;

    @Override
    public Constraint getConstraint()
    {
        final ConstraintBuilder builder = new ConstraintBuilder();

        builder.setName("Concatenation");
        builder.setKind(ConstraintKind.FORMULA_BASED);
        builder.setDescription("Concatenation constraint");

        final NodeVariable x = new NodeVariable(builder.addVariable("x", BIT_VECTOR_ARG_TYPE));
        final NodeVariable y = new NodeVariable(builder.addVariable("y", BIT_VECTOR_ARG_TYPE));
        final NodeVariable z = new NodeVariable(builder.addVariable("z", BIT_VECTOR_RES_TYPE));

        final Formulas formulas = new Formulas();
        builder.setInnerRep(formulas);

        formulas.add(
            new NodeExpr(
                StandardOperation.EQ,
                x,
                new NodeValue(BIT_VECTOR_ARG_TYPE.valueOf("0000", HEX_RADIX))
            )
        );

        formulas.add(
            new NodeExpr(
                StandardOperation.EQ,
                y,
                new NodeValue(BIT_VECTOR_ARG_TYPE.valueOf("ffff", HEX_RADIX))
            )
        );

        formulas.add(
            new NodeExpr(
                StandardOperation.EQ,
                z,
                new NodeExpr(
                    StandardOperation.BVCONCAT,
                    x,
                    y
                )
            )
        );

        return builder.build();
    }

    @Override
    public Iterable<Variable> getExpectedVariables()
    {
        final List<Variable> result = new ArrayList<Variable>();

        result.add(new Variable("x", BIT_VECTOR_ARG_TYPE.valueOf("0000", HEX_RADIX)));
        result.add(new Variable("y", BIT_VECTOR_ARG_TYPE.valueOf("ffff", HEX_RADIX)));
        result.add(new Variable("z", BIT_VECTOR_RES_TYPE.valueOf("0000ffff", HEX_RADIX)));

        return result;
    }
}
