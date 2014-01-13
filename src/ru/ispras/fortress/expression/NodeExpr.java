/*
 * Copyright (c) 2011 ISPRAS
 *
 * Institute for System Programming of Russian Academy of Sciences
 *
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 *
 * All rights reserved.
 *
 * NodeExpr.java, Dec 20, 2011 12:24:03 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.expression;

import java.util.Arrays;

/**
 * The NodeExpr class represents an expression node described by an operation and operands
 *
 * @author Andrei Tatarnikov
 */

public final class NodeExpr extends Node
{
    private final Enum<?> operation;
    private final Node[]   operands;

    /**
     * Creates an expression by performing logic conjunction on two existing expressions.
     * 
     * @param left An existing expression.
     * @param right An existing expression.
     * @return A new expression.
     */

    public static NodeExpr AND(NodeExpr left, NodeExpr right)
    {
        if (null == left)
            throw new NullPointerException();

        if (null == right)
            throw new NullPointerException();

        return new NodeExpr(StandardOperation.AND, left, right);
    }

    /**
     * Creates a new expression by performing logic disjunction on two existing expressions.
     * 
     * @param left An existing expression.
     * @param right An existing expression.
     * @return A new expression.
     */

    public static NodeExpr OR(NodeExpr left, NodeExpr right)
    {
        if (null == left)
            throw new NullPointerException();

        if (null == right)
            throw new NullPointerException();

        return new NodeExpr(StandardOperation.OR, left, right);
    }

    /**
     * Creates a new expression by performing logical negation on an existing expression.
     * 
     * @param expr An existing expression.
     * @return A new expression.
     */

    public static NodeExpr NOT(NodeExpr expr)
    {
        if (null == expr)
            throw new NullPointerException();

        return new NodeExpr(StandardOperation.NOT, expr);
    }

    /**
     * Creates an expression node that has a variable number of operands (from 0 to infinity).
     * 
     * @param operation Operation identifier.
     * @param operands Operands packed into an array of syntax elements.
     */

    public <T extends Enum<?>> NodeExpr(T operation, Node ... operands)
    {
        super(Kind.EXPR);

        if (null == operation)
            throw new NullPointerException();

        if (null == operands)
            throw new NullPointerException();

        this.operation = operation;
        this.operands  = operands;
    }

    /**
     * Returns the number of operands.
     * 
     * @return Number of operands.
     */

    public int getOperandCount()
    {
        return operands.length;
    }

    /**
     * Returns an operand by its index.
     * 
     * @param index Index of the operand.
     * @return An operand of the expression.
     */

    public Node getOperand(int index)
    {
        if (!((0 <= index) && (index < operands.length)))
            throw new IndexOutOfBoundsException();

        return operands[index];
    }

    /**
     * Returns an operation identifier.
     * 
     * @return An operation identifier.
     */

    public Enum<?> getOperationId()
    {
        return operation;
    }

    /* TODO: Not supported in the current version. No implementation for expressions.
    @Override
    public DataType getDataType()
    {
        // TODO: we need to resolve here the type of the expression based
        // on its parameters and some rules.
        assert false : "Not implemented.";
        return null;
    }
    */

    @Override
    public int hashCode()
    {
        final int prime = 31;
        return prime * operation.hashCode() + Arrays.hashCode(operands);
    }

    @Override
    public boolean equals(Object obj)
    {
        if (this == obj) return true;
        if (obj == null) return false;

        if (getClass() != obj.getClass())
            return false;

        final NodeExpr other = (NodeExpr) obj;
        return operation.equals(other.operation) && Arrays.equals(operands, other.operands);
    }

    @Override
    public String toString()
    {
        final StringBuilder sb = new StringBuilder();

        sb.append("(");
        sb.append(operation.name());

        for (Node operand : operands)
        {
            sb.append(" ");
            sb.append(operand.toString());
        }

        sb.append(")");
        return sb.toString();
    }
}
