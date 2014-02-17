/*
 * Copyright (c) 2012 ISPRAS
 *
 * Institute for System Programming of Russian Academy of Sciences
 *
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 *
 * All rights reserved.
 *
 * IntegerOverflow.java, May 4, 2012 2:04:26 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver.samples;

import java.util.ArrayList;
import java.util.List;


import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.*;
import ru.ispras.fortress.solver.constraint.*;

/* The constraint as described in the SMT language:

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
(get-value (rs rt))

Expected output:

sat Values that lead to an overflow: ((rs #x000000009b91b193) (rt #x000000009b91b1b3))

*/

public class IntegerOverflow implements ISampleConstraint
{
    private final int    BIT_VECTOR_LENGTH = 64;
    private final DataType BIT_VECTOR_TYPE = DataType.BIT_VECTOR(BIT_VECTOR_LENGTH);

    private final NodeValue INT_ZERO =
        new NodeValue(
            BIT_VECTOR_TYPE.valueOf("0", 10)
        );

    private final NodeValue INT_BASE_SIZE =
        new NodeValue(
            BIT_VECTOR_TYPE.valueOf("32", 10)
        );

    private final NodeExpr INT_SIGN_MASK =
        new NodeExpr(StandardOperation.BVLSHL, new NodeExpr(StandardOperation.BVNOT, INT_ZERO), INT_BASE_SIZE);

    @Override
    public Constraint getConstraint()
    {
        final ConstraintBuilder builder = new ConstraintBuilder();

        builder.setName("IntegerOverflow");
        builder.setKind(ConstraintKind.FORMULA_BASED);
        builder.setDescription("IntegerOverflow constraint");

        // Unknown variables
        final NodeVariable rs = new NodeVariable(builder.addVariable("rs", BIT_VECTOR_TYPE));
        final NodeVariable rt = new NodeVariable(builder.addVariable("rt", BIT_VECTOR_TYPE));

        final Formulas formulas = new Formulas();
        builder.setInnerRep(formulas);

        formulas.add(IsValidSignedInt(rs));
        formulas.add(IsValidSignedInt(rt));

        formulas.add(
            new NodeExpr(
                StandardOperation.NOT,
                IsValidSignedInt(new NodeExpr(StandardOperation.BVADD, rs, rt))
            )
        );

        formulas.add(
            new NodeExpr(StandardOperation.NOT, new NodeExpr(StandardOperation.EQ, rs, rt))
        );

        return builder.build();
    }

    private NodeExpr IsValidPos(Node arg)
    {
        return new NodeExpr(StandardOperation.EQ, new NodeExpr(StandardOperation.BVAND, arg, INT_SIGN_MASK), INT_ZERO);
    }

    private NodeExpr IsValidNeg(Node arg)
    {
        return new NodeExpr(StandardOperation.EQ, new NodeExpr(StandardOperation.BVAND, arg, INT_SIGN_MASK), INT_SIGN_MASK);
    }

    private NodeExpr IsValidSignedInt(Node arg)
    {
        return new NodeExpr(StandardOperation.OR, IsValidPos(arg), IsValidNeg(arg));
    }

    @Override
    public Iterable<Variable> getExpectedVariables()
    {
        final List<Variable> result = new ArrayList<Variable>();

        result.add(
            new Variable("rs", BIT_VECTOR_TYPE.valueOf("000000009b91b193", 16))
        );

        result.add(
            new Variable("rt", BIT_VECTOR_TYPE.valueOf("000000009b91b1b3", 16))
        );

        return result;
    }
}