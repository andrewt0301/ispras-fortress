/*
 * Copyright (c) 2012 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * CustomOperationsTestCase.java, Oct 4, 2012 12:15:18 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver;

import java.util.ArrayList;
import java.util.List;

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintBuilder;
import ru.ispras.fortress.solver.constraint.ConstraintKind;
import ru.ispras.fortress.solver.constraint.Formulas;
import ru.ispras.fortress.solver.function.Function;

public class CustomOperationsTestCase extends GenericSolverSampleTestBase
{
    @Override
    public CustomOperations createSample()
    {
        return new CustomOperations();
    }
    
    /**
    The semantics of SMT code is the same as with the integer overflow example,
    but in our case we use custom functions.

    The constraint as described in the SMT language:
    
    <pre>
    (define-sort        Int_t () (_ BitVec 64))

    (define-fun      INT_ZERO () Int_t (_ bv0 64))
    (define-fun INT_BASE_SIZE () Int_t (_ bv32 64))
    (define-fun INT_SIGN_MASK () Int_t (bvshl (bvnot INT_ZERO) INT_BASE_SIZE))

    (define-fun IsValidPos ((x!1 Int_t)) Bool (ite (= (bvand x!1 INT_SIGN_MASK) INT_ZERO) true false))
    (define-fun IsValidNeg ((x!1 Int_t)) Bool (ite (= (bvand x!1 INT_SIGN_MASK) INT_SIGN_MASK) true false))
    (define-fun IsValidSignedInt ((x!1 Int_t)) Bool (ite (or (IsValidPos x!1) (IsValidNeg x!1)) true false))

    (declare-const rs Int_t)
    (declare-const rt Int_t)

    ; rt and rs must contain valid sign-extended 32-bit values (bits 63..31 equal)
    (assert (IsValidSignedInt rs))
    (assert (IsValidSignedInt rt))

    ; the condition for an overflow: the summation result is not a valid sign-extended 32-bit value
    (assert (not (IsValidSignedInt (bvadd rs rt))))

    ; just in case: rs and rt are not equal (to make the results more interesting)
    (assert (not (= rs rt)))

    (check-sat)

    (echo "Values that lead to an overflow:")
    (get-value (rs rt))</pre>

    Expected output (values that lead to an overflow):

    <pre>
    sat ((rs #x000000009b91b193) (rt #x000000009b91b1b3))</pre>
    */

    public static class CustomOperations implements ISampleConstraint
    {
        private final int  BV_LENGTH = 64;
        private final DataType Int_t = DataType.BIT_VECTOR(BV_LENGTH);

        private enum ECustomOperation
        {
            INT_ZERO,
            INT_BASE_SIZE,
            INT_SIGN_MASK,
            IS_VALID_POS,
            IS_VALID_NEG,
            IS_VALID_SIGNED_INT
        }

        private void registerCustomOperations(Solver solver)
        {
            registerINT_ZERO(solver);
            registerINT_BASE_SIZE(solver);
            registerINT_SIGN_MASK(solver);
            registerIS_VALID_POS(solver);
            registerIS_VALID_NEG(solver);
            registerIS_VALID_SIGNED_INT(solver);
        }

        // (define-fun INT_ZERO () Int_t (_ bv0 64))
        private void registerINT_ZERO(Solver solver)
        {
            final Node body = new NodeValue(Int_t.valueOf("0", 10));
            solver.addCustomOperation(
                new Function(ECustomOperation.INT_ZERO, Int_t, body)
            );
        }

        // (define-fun INT_BASE_SIZE () Int_t (_ bv32 64))
        private void registerINT_BASE_SIZE(Solver solver)
        {
            final Node body = new NodeValue(Int_t.valueOf("32", 10));
            solver.addCustomOperation(
                new Function(ECustomOperation.INT_BASE_SIZE, Int_t, body)
            );
        }

        // (define-fun INT_SIGN_MASK () Int_t (bvshl (bvnot INT_ZERO) INT_BASE_SIZE))
        private void registerINT_SIGN_MASK(Solver solver)
        {
            final Node body =
                new NodeOperation(
                    StandardOperation.BVLSHL,
                    new NodeOperation(StandardOperation.BVNOT, new NodeOperation(ECustomOperation.INT_ZERO)),
                    new NodeOperation(ECustomOperation.INT_BASE_SIZE)
                    );

            solver.addCustomOperation(
                new Function(ECustomOperation.INT_SIGN_MASK, Int_t, body)
            );
        }

        // (define-fun IS_VALID_POS ((x!1 Int_t)) Bool (ite (= (bvand x!1 INT_SIGN_MASK) INT_ZERO) true false))
        private void registerIS_VALID_POS(Solver solver)
        {
            final Variable param = new Variable("x", Int_t);

            final Node body = new NodeOperation(
                StandardOperation.EQ,
                new NodeOperation(
                    StandardOperation.BVAND,
                    new NodeVariable(param),
                    new NodeOperation(ECustomOperation.INT_SIGN_MASK)
                ),
                new NodeOperation(ECustomOperation.INT_ZERO)
            );

            solver.addCustomOperation(
                new Function(ECustomOperation.IS_VALID_POS, DataType.BOOLEAN, body, param)
            );
        }

        // (define-fun IS_VALID_NEG ((x!1 Int_t)) Bool (ite (= (bvand x!1 INT_SIGN_MASK) INT_SIGN_MASK) true false))
        private void registerIS_VALID_NEG(Solver solver)
        {
            final Variable param = new Variable("x", Int_t);

            final Node body = new NodeOperation(
                StandardOperation.EQ,
                new NodeOperation(
                    StandardOperation.BVAND,
                    new NodeVariable(param),
                    new NodeOperation(ECustomOperation.INT_SIGN_MASK)
                    ),
                new NodeOperation(ECustomOperation.INT_SIGN_MASK)
            );

            solver.addCustomOperation(
                new Function(ECustomOperation.IS_VALID_NEG, DataType.BOOLEAN, body, param)
            );
        }

        // (define-fun IS_VALID_SIGNED_INT ((x!1 Int_t)) Bool (ite (or (IsValidPos x!1) (IsValidNeg x!1)) true false))
        private void registerIS_VALID_SIGNED_INT(Solver solver)
        {
            final Variable param = new Variable("x", Int_t);

            final Node body = new NodeOperation(
                StandardOperation.OR,
                new NodeOperation(ECustomOperation.IS_VALID_POS, new NodeVariable(param)),
                new NodeOperation(ECustomOperation.IS_VALID_NEG, new NodeVariable(param))
            );

            solver.addCustomOperation(
                new Function(ECustomOperation.IS_VALID_SIGNED_INT, DataType.BOOLEAN, body, param)
            );
        }

        @Override
        public Constraint getConstraint()
        {
            final Solver solver = SolverId.Z3_TEXT.getSolver();
            assert null != solver;

            registerCustomOperations(solver);

            final ConstraintBuilder builder = new ConstraintBuilder();

            builder.setName("CustomOpIntegerOverflow");
            builder.setKind(ConstraintKind.FORMULA_BASED);
            builder.setDescription("Custom Operation IntegerOverflow constraint");

            // Unknown variables

            // (declare-const rs Int_t)
            final NodeVariable rs = new NodeVariable(builder.addVariable("rs", Int_t));
            // (declare-const rt Int_t)
            final NodeVariable rt = new NodeVariable(builder.addVariable("rt", Int_t));

            final Formulas formulas = new Formulas();
            builder.setInnerRep(formulas);

            // ; rt and rs must contain valid sign-extended 32-bit values (bits 63..31 equal)

            // (assert (IsValidSignedInt rs))
            formulas.add(
                new NodeOperation(ECustomOperation.IS_VALID_SIGNED_INT, rs)
            );

            // (assert (IsValidSignedInt rt))
            formulas.add(
                new NodeOperation(ECustomOperation.IS_VALID_SIGNED_INT, rt)
            );

            // ; the condition for an overflow: the summation result is not a valid sign-extended 32-bit value

            // (assert (not (IsValidSignedInt (bvadd rs rt))))
            formulas.add(
                new NodeOperation(
                    StandardOperation.NOT,
                    new NodeOperation(
                        ECustomOperation.IS_VALID_SIGNED_INT,
                        new NodeOperation(StandardOperation.BVADD, rs, rt)
                    )
                )
            );

            // ; just in case: rs and rt are not equal (to make the results more interesting)
            // (assert (not (= rs rt)))

            formulas.add(
                new NodeOperation(StandardOperation.NOT, new NodeOperation(StandardOperation.EQ, rs, rt))
            );

            return builder.build();
        }

        @Override
        public Iterable<Variable> getExpectedVariables()
        {
            final List<Variable> result = new ArrayList<Variable>();

            result.add(new Variable("rs", Int_t.valueOf("000000009b91b193", 16)));
            result.add(new Variable("rt", Int_t.valueOf("000000009b91b1b3", 16)));

            return result;
        }
    }

}
