/*
 * Copyright (c) 2013 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * FunctionFactory.java, Dec 16, 2013 7:22:13 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver.function;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.DataTypeId;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.*;

/** 
 * This class contains methods for performing special custom operations
 * (first of all, some specific operations from HDL) into
 * Constraint Solver API representation.
 *
 * @author Sergey Smolov (ssedai@ispras.ru)
 */

public final class FunctionFactory
{
    public static Function makeAbs(Variable operand)
    {
        checkNotNull(operand);
        checkLogicNumeric(operand);

        final DataType returnType = operand.getData().getType();
        final Node operandNode = new NodeVariable(operand);

        final Data zeroData;
        switch (returnType.getTypeId())
        {
            case LOGIC_INTEGER: zeroData = Data.newInteger(0); break;
            case LOGIC_REAL:    zeroData = Data.newReal(0);    break;
            default:            zeroData = null;               assert false;
        }

        final NodeExpr body = new NodeExpr(
            StandardOperation.ITE,
            new NodeExpr(StandardOperation.GREATEREQ, operandNode, new NodeValue(zeroData)),
            operandNode,
            new NodeExpr(StandardOperation.MINUS, operandNode)
        );

        return new Function(returnType, body, operand);
    }

    public static Function makeMin(Variable left, Variable right)
    {
        checkNotNull(left);
        checkNotNull(right);

        checkEqualTypes(left, right);
        checkLogicNumeric(left);
        checkLogicNumeric(right);

        final DataType returnType = left.getData().getType();
        final Node leftNode = new NodeVariable(left);
        final Node rightNode = new NodeVariable(right);

        final NodeExpr body = new NodeExpr(
            StandardOperation.ITE,
            new NodeExpr(StandardOperation.GREATEREQ, leftNode, rightNode),
            rightNode,
            leftNode
        );

        return new Function(returnType, body, left, right);
    }

    public static Function makeMax(Variable left, Variable right)
    {
        checkNotNull(left);
        checkNotNull(right);

        checkEqualTypes(left, right);
        checkLogicNumeric(left);
        checkLogicNumeric(right);

        final DataType returnType = left.getData().getType();
        final Node leftNode = new NodeVariable(left);
        final Node rightNode = new NodeVariable(right);

        final NodeExpr body = new NodeExpr(
            StandardOperation.ITE,
            new NodeExpr(StandardOperation.GREATEREQ, leftNode, rightNode),
            leftNode,
            rightNode
        );

        return new Function(returnType, body, left, right);
    }
    
    public static Function makeBVANDR(Variable operand)
    {
        checkNotNull(operand);
        checkBitVector(operand);

        final NodeExpr body = new NodeExpr(
            StandardOperation.ITE, makeBVEqualsAllOnes(operand), BIT_TRUE, BIT_FALSE);

        return new Function(BIT_BOOL, body, operand);
    }

    public static Function makeBVNANDR(Variable operand)
    {
        checkNotNull(operand);
        checkBitVector(operand);

        final NodeExpr body = new NodeExpr(
            StandardOperation.ITE, makeBVEqualsAllOnes(operand), BIT_FALSE, BIT_TRUE);

        return new Function(BIT_BOOL, body, operand);
    }

    public static Function makeBVORR(Variable operand)
    {
        checkNotNull(operand);
        checkBitVector(operand);

        final NodeExpr body = new NodeExpr(
            StandardOperation.ITE, makeBVEqualsAllZeros(operand), BIT_FALSE, BIT_TRUE);

        return new Function(BIT_BOOL, body, operand);
    }

    public static Function makeBVNORR(Variable operand)
    {
        checkNotNull(operand);
        checkBitVector(operand);

        final NodeExpr body = new NodeExpr(
            StandardOperation.ITE, makeBVEqualsAllZeros(operand), BIT_TRUE, BIT_FALSE);

        return new Function(BIT_BOOL, body, operand);
    }

    /*
    // TODO: NOT IMPLEMENTED
    public static Function makeBVXORR(Variable operand)
    {
        checkNotNull(operand);
        checkBitVector(operand);

        final Node body = null;
        return new Function(BIT_BOOL, body, operand);
    }

    // TODO: NOT IMPLEMENTED
    public static Function makeBVXNORR(Variable operand)
    {
        checkNotNull(operand);
        checkBitVector(operand);

        final Node body = null;
        return new Function(BIT_BOOL, body, operand);
    }
    */

    private static void checkNotNull(Object o)
    {
        if (null == o)
            throw new NullPointerException();
    }

    private static void checkEqualTypes(Variable left, Variable right)
    {
        if (left.getData().getType().equals(right.getData().getType()))
            return;

        throw new IllegalArgumentException(
            String.format(ERR_UNEQUAL_ARG_TYPES,
                left.getName(), left.getData().getType(), right.getName(), right.getData().getType()));
    }

    private static void checkLogicNumeric(Variable operand)
    {
        final DataType type = operand.getData().getType();
        final DataTypeId typeId = type.getTypeId();

        if ((DataTypeId.LOGIC_INTEGER == typeId) || (DataTypeId.LOGIC_REAL == typeId))
            return;

        throw new IllegalArgumentException(
            String.format(ERR_UNSUPPORTED_ARG_TYPE,
                operand.getName(), type, DataTypeId.LOGIC_INTEGER + " and " + DataTypeId.LOGIC_REAL));
    }

    private static void checkBitVector(Variable operand)
    {
        final DataType type = operand.getData().getType();
        final DataTypeId typeId = type.getTypeId();

        if (DataTypeId.BIT_VECTOR == typeId)
            return;

        throw new IllegalArgumentException(
            String.format(ERR_UNSUPPORTED_ARG_TYPE, operand.getName(), type, DataTypeId.BIT_VECTOR));
    }

    private static final Node makeBVEqualsAllZeros(Variable operand)
    {
        final DataType operandType = operand.getData().getType();

        final NodeVariable operandNode = new NodeVariable(operand);
        final NodeValue zeroNode = new NodeValue(Data.newBitVector(0, operandType.getSize()));

        return new NodeExpr(StandardOperation.EQ, operandNode, zeroNode);
    }

    private static final Node makeBVEqualsAllOnes(Variable operand)
    {
        final DataType operandType = operand.getData().getType();

        final NodeVariable operandNode = new NodeVariable(operand);
        final NodeValue zeroNode = new NodeValue(Data.newBitVector(0, operandType.getSize()));

        return new NodeExpr(StandardOperation.EQ, operandNode, new NodeExpr(StandardOperation.BVNOT, zeroNode));
    }

    private static final int BIT_BOOL_SIZE   = 1;
    private static final DataType  BIT_BOOL  = DataType.BIT_VECTOR(BIT_BOOL_SIZE);
    private static final NodeValue BIT_TRUE  = new NodeValue(Data.newBitVector(1, BIT_BOOL_SIZE));
    private static final NodeValue BIT_FALSE = new NodeValue(Data.newBitVector(0, BIT_BOOL_SIZE));

    private static final String ERR_UNEQUAL_ARG_TYPES =
        "Arguments %s (%s) and %s (%s) have unequal types.";

    private static final String ERR_UNSUPPORTED_ARG_TYPE =
        "Argument %s (%s) has an unsupported type. Expected types: %s.";
}
