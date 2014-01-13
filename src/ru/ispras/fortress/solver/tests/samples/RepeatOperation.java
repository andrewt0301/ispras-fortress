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

(declare-const x (_ BitVec 4))
(declare-const y (_ BitVec 16))
(assert (= x #x5))
(assert (= y ((_ repeat 4) x)))
(check-sat)
(get-value (x y))
(exit)

Expected output:
sat
((x #x5)
 (y #x5555))

*/

public class RepeatOperation implements ISampleConstraint
{
    private static final int      BIT_VECTOR_ARG_SIZE = 4;
    private static final DataType BIT_VECTOR_ARG_TYPE = DataType.BIT_VECTOR(BIT_VECTOR_ARG_SIZE);
    private static final int      BIT_VECTOR_RES_SIZE = 16;
    private static final DataType BIT_VECTOR_RES_TYPE = DataType.BIT_VECTOR(BIT_VECTOR_RES_SIZE);
    private static final DataType INT_TYPE            = DataType.INTEGER;

    private static final int HEX_RADIX = 16;
    private static final int DEC_RADIX = 10;

    @Override
    public Constraint getConstraint()
    {
        final ConstraintBuilder builder = new ConstraintBuilder();

        builder.setName("RepeatOperation");
        builder.setKind(ConstraintKind.FORMULA_BASED);
        builder.setDescription("RepeatOperation constraint");

        final NodeVariable x = new NodeVariable(builder.addVariable("x", BIT_VECTOR_ARG_TYPE));
        final NodeVariable y = new NodeVariable(builder.addVariable("y", BIT_VECTOR_RES_TYPE));

        final Formulas formulas = new Formulas();
        builder.setInnerRep(formulas);

        formulas.add(
            new NodeExpr(
                StandardOperation.EQ,
                x,
                new NodeValue(BIT_VECTOR_ARG_TYPE.valueOf("5", HEX_RADIX))
            )
        );

        formulas.add(
            new NodeExpr(
                StandardOperation.EQ,
                y,
                new NodeExpr(
                    StandardOperation.BVREPEAT,
                    Transform.reduce(
                        ReduceOptions.NEW_INSTANCE,
                        new NodeExpr(
                            StandardOperation.ADD,
                            new NodeValue(INT_TYPE.valueOf("2", DEC_RADIX)),
                            new NodeValue(INT_TYPE.valueOf("2", DEC_RADIX))
                        )
                    ),
                    x
                )
            )
        );

        return builder.build();
    }

    @Override
    public Iterable<Variable> getExpectedVariables()
    {
        final List<Variable> result = new ArrayList<Variable>();

        result.add(new Variable("x", BIT_VECTOR_ARG_TYPE.valueOf("5", HEX_RADIX)));
        result.add(new Variable("y", BIT_VECTOR_RES_TYPE.valueOf("5555", HEX_RADIX)));

        return result;
    }
}
