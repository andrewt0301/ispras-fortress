package ru.ispras.fortress.solver.samples;

import java.util.ArrayList;
import java.util.List;


import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.*;
import ru.ispras.fortress.solver.constraint.*;

/* The constraint as described in the SMT-LIB language:

(declare-const x (_ BitVec 32))
(assert (bvugt x (_ bv100 32)))
(check-sat)
(get-value (x))
(exit)

Expected output: sat ((x #x00000070))

*/
public class BVUGTOperation implements ISampleConstraint
{
    protected static final int      BIT_VECTOR_SIZE = 32;
    protected static final DataType BIT_VECTOR_TYPE = DataType.BIT_VECTOR(BIT_VECTOR_SIZE);

    public Constraint getConstraint()
    {
        final ConstraintBuilder builder = new ConstraintBuilder();

        builder.setName("PowerOfTwo");
        builder.setKind(ConstraintKind.FORMULA_BASED);
        builder.setDescription("PowerOfTwo constraint");

        final NodeVariable x = new NodeVariable(builder.addVariable("x", BIT_VECTOR_TYPE));

        final Formulas formulas = new Formulas();
        builder.setInnerRep(formulas);

        formulas.add(
            new NodeExpr(
                StandardOperation.BVUGT,
                x,
                new NodeValue(BIT_VECTOR_TYPE.valueOf("100", 10))
            )
        );

        return builder.build();
    }

    public Iterable<Variable> getExpectedVariables()
    {
        final List<Variable> result = new ArrayList<Variable>();

        result.add( new Variable("x", BIT_VECTOR_TYPE.valueOf("112", 10)));

        return result;
    }

}
