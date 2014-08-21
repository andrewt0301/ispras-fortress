/*
 * Copyright (c) 2012 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * SimpleBitVectorTestCase.java, Jan 13, 2012 2:10:58 PM Andrei Tatarnikov
 */

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

public class SimpleBitVectorTestCase extends GenericSolverSampleTestBase
{
    @Override
    public SimpleBitVector createSample()
    {
        return new SimpleBitVector();
    }

    /** The constraint as described in the SMT language:

    <pre>
    (declare-const a (_ BitVec 3))
    (declare-const b (_ BitVec 3))
    (assert (not (= a b)))
    (assert (= (bvor a b) #b111))
    (assert (= (bvand a b) #b000))
    (assert (= (bvshl a (_ bv3 3))(bvsmod a (_ bv2 3))))
    (check-sat)
    (get-value (a b))
    (exit)</pre>

    Expected output: sat ((a #b010) (b #b101))
    */

    public static class SimpleBitVector implements ISampleConstraint
    {
        private static final int      BIT_VECTOR_SIZE = 3;
        private static final DataType BIT_VECTOR_TYPE = DataType.BIT_VECTOR(BIT_VECTOR_SIZE);

        @Override
        public Constraint getConstraint()
        {
            final ConstraintBuilder builder = new ConstraintBuilder();

            builder.setName("SimpleBitVector");
            builder.setKind(ConstraintKind.FORMULA_BASED);
            builder.setDescription("SimpleBitVector constraint");

            final NodeVariable a = new NodeVariable(builder.addVariable("a", BIT_VECTOR_TYPE));
            final NodeVariable b = new NodeVariable(builder.addVariable("b", BIT_VECTOR_TYPE));

            final Formulas formulas = new Formulas();
            builder.setInnerRep(formulas);

            formulas.add(
                new NodeOperation(
                    StandardOperation.NOT,
                    new NodeOperation(StandardOperation.EQ, a, b)
                )
            );

            formulas.add(
                new NodeOperation(
                    StandardOperation.EQ,
                    new NodeOperation(StandardOperation.BVOR, a, b),
                    new NodeValue(BIT_VECTOR_TYPE.valueOf("111", 2))
                )
            );

            formulas.add(
                new NodeOperation(
                    StandardOperation.EQ,
                    new NodeOperation(StandardOperation.BVLSHL, a, new NodeValue(BIT_VECTOR_TYPE.valueOf("3", 10))),
                    new NodeOperation(StandardOperation.BVSMOD, a, new NodeValue(BIT_VECTOR_TYPE.valueOf("2", 10)))
                )
            );

            formulas.add(
                new NodeOperation(
                    StandardOperation.EQ,
                    new NodeOperation(StandardOperation.BVAND, a, b),
                    new NodeValue(BIT_VECTOR_TYPE.valueOf("0", 2))
                )
            );

            return builder.build();
        }

        @Override
        public Iterable<Variable> getExpectedVariables()
        {
            final List<Variable> result = new ArrayList<Variable>();

            result.add(new Variable("a", BIT_VECTOR_TYPE.valueOf("010", 2)));
            result.add(new Variable("b", BIT_VECTOR_TYPE.valueOf("101", 2)));

            return result;
        }
    }
}
