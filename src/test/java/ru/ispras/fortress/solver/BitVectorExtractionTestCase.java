package ru.ispras.fortress.solver;

import java.util.Arrays;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.*;
import ru.ispras.fortress.solver.constraint.*;

/** The constraint as described in the SMT-LIB language:

<pre>
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 8))
(assert (= x (_ bv100 257)))
(assert (= y ((_ extract 0 7) x))
(check-sat)
(get-value (x))
(exit)</pre>

Expected output:

<pre>
sat ((x #x00000070))</pre>
*/

public class BitVectorExtractionTestCase extends GenericSolverSampleTestBase
{
    @Override
    public ISampleConstraint createSample()
    {
        return new BitVectorExtractionConstraint();
    }
}

final class BitVectorExtractionConstraint implements ISampleConstraint
{
    private static final DataType BitVector32 = DataType.BIT_VECTOR(32);
    private static final DataType BitVector8 = DataType.BIT_VECTOR(8);

    private static Node INTEGER(int n)
    {
        return new NodeValue(Data.newInteger(n));
    }

    public Constraint getConstraint()
    {
        final ConstraintBuilder builder = new ConstraintBuilder();

        builder.setName("BVEXTRACT");
        builder.setKind(ConstraintKind.FORMULA_BASED);
        builder.setDescription("Bitvector extraction constraint");

        final NodeVariable x = new NodeVariable(builder.addVariable("x", BitVector32));
        final NodeVariable y = new NodeVariable(builder.addVariable("y", BitVector8));

        final Formulas formulas = new Formulas();
        builder.setInnerRep(formulas);

        formulas.add(
            new NodeOperation(
                StandardOperation.EQ,
                x,
                new NodeValue(BitVector32.valueOf("257", 10))
            )
        );
        formulas.add(
            new NodeOperation(
                StandardOperation.EQ,
                y,
                new NodeOperation(StandardOperation.BVEXTRACT, INTEGER(7), INTEGER(0), x)));

        return builder.build();
    }

    public Iterable<Variable> getExpectedVariables()
    {
        return Arrays.asList(
            new Variable("x", BitVector32.valueOf("257", 10)),
            new Variable("y", BitVector8.valueOf("1", 10)));
    }
}
