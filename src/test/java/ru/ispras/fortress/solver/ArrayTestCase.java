package ru.ispras.fortress.solver;

import java.util.ArrayList;
import java.util.List;

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.*;
import ru.ispras.fortress.solver.constraint.*;

/** The constraint as described in the SMT-LIB language:

<pre>
(define-sort ARRAY_TYPE () (Array Int Int))
(declare-fun a () ARRAY_TYPE)
(declare-fun v () ARRAY_TYPE)
(assert (= a (store v 37 37)))
(check-sat)
(get-value (a))
(get-value (v))
(get-model)
(exit)</pre>

Expected output:

<pre>
sat ((x #x00000070))</pre>
*/

public class ArrayTestCase extends GenericSolverSampleTestBase
{
    @Override
    public ISampleConstraint createSample()
    {
        return new ArrayInvariant();
    }
}

class ArrayInvariant implements ISampleConstraint
{
    private static final DataType ARRAY_TYPE = DataType.MAP(DataType.INTEGER, DataType.INTEGER);

    public Constraint getConstraint()
    {
        final ConstraintBuilder builder = new ConstraintBuilder();

        builder.setName("ArrayInvariant");
        builder.setKind(ConstraintKind.FORMULA_BASED);
        builder.setDescription("ArrayInvariant constraint");

        final NodeVariable a = new NodeVariable(builder.addVariable("a", ARRAY_TYPE));
        final NodeVariable v = new NodeVariable(builder.addVariable("v", ARRAY_TYPE));

        final NodeValue value = new NodeValue(DataType.INTEGER.valueOf("37", 10));
        final Node stored = new NodeExpr(StandardOperation.STORE, v, value, value);

        final Formulas formulas = new Formulas();
        builder.setInnerRep(formulas);

        formulas.add(new NodeExpr(StandardOperation.EQ, a, stored));

        return builder.build();
    }

    public Iterable<Variable> getExpectedVariables()
    {
        final List<Variable> result = new ArrayList<Variable>();

        result.add( new Variable("a", ARRAY_TYPE.valueOf("((37:37))", 10)));
        result.add( new Variable("v", ARRAY_TYPE.valueOf("()", 10)));

        return result;
    }
}
