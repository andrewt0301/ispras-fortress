/*
 * Copyright (c) 2011 ISPRAS (www.ispras.ru)
 *
 * Institute for System Programming of Russian Academy of Sciences
 *
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 *
 * All rights reserved.
 *
 * NodeExpr.java, Dec 20, 2011 12:24:03 PM Andrei Tatarnikov
 * 
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not
 * use this file except in compliance with the License. You may obtain a copy of
 * the License at
 * 
 * http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations under
 * the License.
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
     * Constructor for making deep copies. The operation field is immutable
     * and, therefore, it copied by reference. The operands array is cloned
     * because it contains nodes that must be cloned to create a fully
     * independent copy of an expression. 
     * 
     * @param nodeExpr Node expression object to be copied.
     */

    private NodeExpr(NodeExpr nodeExpr)
    {
        super(nodeExpr);

        this.operation = nodeExpr.operation;
        this.operands  = new Node[nodeExpr.operands.length];

        for (int index = 0; index < nodeExpr.operands.length; index++)
            this.operands[index] = nodeExpr.operands[index].deepCopy();
    }

    /**
     * {@inheritDoc}
     */

    @Override
    public Node deepCopy()
    {
        return new NodeExpr(this);
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
