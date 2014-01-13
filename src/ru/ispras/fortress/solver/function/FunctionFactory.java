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
    public static Function makeAbs(NodeVariable operand)
    {
        if (null == operand)
            throw new NullPointerException();

        Data data = null;
        switch (operand.getData().getType().getTypeId())
        {
            case LOGIC_INTEGER:
                data = Data.createInteger(0);
                break;
            case LOGIC_REAL:
                data = Data.createReal(0);
                break;
            default:
                throw new IllegalArgumentException(
                    "Type " + operand.getData().getType() + " is not supported here.");
        }

        final Variable parameter = new Variable("x", data);

        final NodeExpr body = new NodeExpr(
            StandardOperation.ITE,
            new NodeExpr(StandardOperation.GREATEREQ, operand, new NodeValue(data)),
            operand,
            new NodeExpr(StandardOperation.MINUS, operand)
        );

        return new Function(operand.getData().getType(), body, parameter);
    }

    public static Function makeMin(NodeVariable left, NodeVariable right)
    {
        if (null == left)
            throw new NullPointerException();
        
        if (null == right)
            throw new NullPointerException();

        final Data data = Data.createReal(0);

        //check whether both operands are INT or REAL
        if (!areLogic(left, right))
        {
            throw new IllegalArgumentException(
                String.format("Unsupported argument types: %s and %s",
                    left.getData().getType(), right.getData().getType()));
        }

        final Variable  leftParameter = new Variable("x", data);
        final Variable rightParameter = new Variable("y", data);

        final NodeExpr body = new NodeExpr(
            StandardOperation.ITE,
            new NodeExpr(StandardOperation.GREATEREQ, left, right),
            right,
            left
        );

        return new Function(data.getType(), body, leftParameter, rightParameter);
    }

    public static Function makeMax(NodeVariable left, NodeVariable right)
    {
        if (null == left)
            throw new NullPointerException();
        
        if (null == right)
            throw new NullPointerException();

        final Data data = Data.createReal(0);

        //check whether both operands are INT or REAL
        if (!areLogic(left, right))
        {
            throw new IllegalArgumentException(
                String.format("Unsupported argument types: %s and %s",
                   left.getData().getType(), right.getData().getType()));
        }

        final Variable leftParameter  = new Variable("x", data);
        final Variable rightParameter = new Variable("y", data);

        final NodeExpr body = new NodeExpr(
            StandardOperation.ITE,
            new NodeExpr(StandardOperation.GREATEREQ, left, right),
            left,
            right
        );

        return new Function(data.getType(), body, leftParameter, rightParameter);
    }

    private static boolean areLogic(NodeVariable ... variables)
    {
        for (NodeVariable v : variables)
        {
            final DataTypeId typeId = v.getData().getType().getTypeId();

            if ((typeId!= DataTypeId.LOGIC_INTEGER) && (typeId != DataTypeId.LOGIC_REAL))
                return false;
        }

        return true;
    }
}
