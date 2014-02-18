/*
 * Copyright (c) 2012 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * InputParametersTestCase.java, Oct 4, 2012 11:29:56 AM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver;

import java.util.ArrayList;
import java.util.List;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.NodeExpr;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintBuilder;
import ru.ispras.fortress.solver.constraint.ConstraintKind;
import ru.ispras.fortress.solver.constraint.Formulas;

public class InputParametersTestCase extends GenericSolverSampleTestBase
{
    @Override
    public Constraint getConstraint()
    {
        final Constraint constraint = super.getConstraint();

        constraint.setVariableValue("b", Data.newBitVector(2, 16));
        constraint.setVariableValue("c", Data.newBitVector(5, 16));

        return constraint;
    }

    @Override
    public InputParameters createSample()
    {
        return new InputParameters();
    }

    /** The constraint as described in the SMT-LIB language:

    <pre>
    (declare-const a (_ BitVec 16))
    (declare-const b (_ BitVec 16))
    (declare-const c (_ BitVec 16))

    ;(assert (= a #x0003)) ; assumed input value
    ;(assert (= c #x0005)) ; assumed input value

    (assert (= (bvadd a b) c))

    (check-sat)
    (get-value (a b c))
    (exit)</pre>

    Expected output:

    <pre>
    sat ((a #x0003)(b #x0002)(c #x0005))</pre>
    */

    public static class InputParameters implements ISampleConstraint
    {
        private static final int      BIT_VECTOR_SIZE = 16;
        private static final DataType BIT_VECTOR_TYPE = DataType.BIT_VECTOR(BIT_VECTOR_SIZE);

        public Constraint getConstraint()
        {
            final ConstraintBuilder builder = new ConstraintBuilder();

            builder.setName("InputParameters");
            builder.setKind(ConstraintKind.FORMULA_BASED);
            builder.setDescription("InputParameters constraint");

            final NodeVariable a = new NodeVariable(builder.addVariable("a", BIT_VECTOR_TYPE));
            final NodeVariable b = new NodeVariable(builder.addVariable("b", BIT_VECTOR_TYPE));
            final NodeVariable c = new NodeVariable(builder.addVariable("c", BIT_VECTOR_TYPE));

            final Formulas formulas = new Formulas();
            builder.setInnerRep(formulas);

            formulas.add(
                new NodeExpr(
                    StandardOperation.EQ,
                    new NodeExpr(StandardOperation.BVADD, a, b),
                    c
                )
            );

            return builder.build();
        }

        public Iterable<Variable> getExpectedVariables()
        {
            final List<Variable> result = new ArrayList<Variable>();

            result.add(new Variable("a", BIT_VECTOR_TYPE.valueOf("3", 16)));

            return result;
        }
    }
}
