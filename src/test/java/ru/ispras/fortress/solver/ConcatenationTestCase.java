package ru.ispras.fortress.solver;

import java.util.ArrayList;
import java.util.List;

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintBuilder;
import ru.ispras.fortress.solver.constraint.ConstraintKind;
import ru.ispras.fortress.solver.constraint.Formulas;

public class ConcatenationTestCase extends GenericSolverSampleTestBase
{
    @Override
    public ISampleConstraint createSample()
    {
        return new Concatenation();
    }

    /** The constraint as described in the SMT language:

    <pre>
    (declare-const x (_ BitVec 16))
    (declare-const y (_ BitVec 16))
    (declare-const z (_ BitVec 32))
    (assert (= x #x0000))
    (assert (= y #xffff))
    (assert (= z (concat x y)))
    (check-sat)
    (get-value (x y z))
    (exit)</pre>

    Expected output: 

    <pre>
    sat ((z #x0000ffff))</pre>
    */

    public static class Concatenation implements ISampleConstraint
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
                new NodeOperation(
                    StandardOperation.EQ,
                    x,
                    new NodeValue(BIT_VECTOR_ARG_TYPE.valueOf("0000", HEX_RADIX))
                )
            );

            formulas.add(
                new NodeOperation(
                    StandardOperation.EQ,
                    y,
                    new NodeValue(BIT_VECTOR_ARG_TYPE.valueOf("ffff", HEX_RADIX))
                )
            );

            formulas.add(
                new NodeOperation(
                    StandardOperation.EQ,
                    z,
                    new NodeOperation(
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
}
