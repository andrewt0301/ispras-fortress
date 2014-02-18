/*
 * Copyright (c) 2012 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * PowerOfTwoBitVectorTestCase.java, Jan 13, 2012 2:27:33 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver;

import java.util.ArrayList;
import java.util.List;

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.NodeExpr;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintBuilder;
import ru.ispras.fortress.solver.constraint.ConstraintKind;
import ru.ispras.fortress.solver.constraint.Formulas;

public class PowerOfTwoBitVectorTestCase extends GenericSolverSampleTestBase
{
    @Override
    public PowerOfTwo createSample()
    {
        return new PowerOfTwo();
    }

    /** The constraint as described in the SMT-LIB language:

    <pre>
    (declare-const x (_ BitVec 32))
    (assert (bvugt x (_ bv100 32)))
    (assert (bvult x (_ bv200 32)))
    (assert (= (bvand x (bvsub x (_ bv1 32))) (_ bv0 32)))
    (check-sat)
    (get-value (x))
    (exit)</pre>

    Expected output:

    <pre>
    sat ((x #x00000080))</pre>
    */

    public static class PowerOfTwo implements ISampleConstraint
    {
        private static final int      BIT_VECTOR_SIZE = 32;
        private static final DataType BIT_VECTOR_TYPE = DataType.BIT_VECTOR(BIT_VECTOR_SIZE);

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

            formulas.add(
                new NodeExpr(
                    StandardOperation.BVULT,
                    x,
                    new NodeValue(BIT_VECTOR_TYPE.valueOf("200", 10))
                )
            );

            formulas.add(
                new NodeExpr(
                    StandardOperation.EQ,
                    new NodeExpr(
                        StandardOperation.BVAND,
                        x, 
                        new NodeExpr(
                            StandardOperation.BVSUB,
                            x,
                            new NodeValue(BIT_VECTOR_TYPE.valueOf("1", 10))
                        )
                    ),
                    new NodeValue(BIT_VECTOR_TYPE.valueOf("0", 10))
                )
            );

            return builder.build();
        }

        public Iterable<Variable> getExpectedVariables()
        {
            final List<Variable> result = new ArrayList<Variable>();

            result.add(new Variable("x", BIT_VECTOR_TYPE.valueOf("128", 10)));

            return result;
        }
    }
}
