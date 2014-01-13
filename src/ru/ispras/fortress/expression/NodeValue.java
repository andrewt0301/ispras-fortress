/*
 * Copyright (c) 2011 ISPRAS
 *
 * Institute for System Programming of Russian Academy of Sciences
 *
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 *
 * All rights reserved.
 *
 * NodeValue.java, Dec 20, 2011 12:23:40 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.expression;

import ru.ispras.fortress.data.Data;

/**
 * The NodeValue class represents a node that stores a constant value.
 * The class serves as an adapter to allow Data to be used in an expression.
 *
 * @author Andrei Tatarnikov
 */

public final class NodeValue extends Node
{
    private final Data data;

    /**
     * Creates a value syntax element based on a data object.
     * 
     * @param data A data object.
     */

    public NodeValue(Data data)
    {
        super(Kind.VALUE);

        if (null == data)
            throw new NullPointerException();

        this.data = data;
    }

    /**
     * Returns the data object that encapsulates the value.
     * 
     * @return A data object.
     */

    public Data getData()
    {
        return data;
    }

    /**
     * Returns an object that stores a data value. The exact type of the object
     * returned by the method depends on the data type.
     * 
     * @return An object that store the value of the constant.
     */

    public Object getValue()
    {
        return data.getValue();
    }

    /* TODO: Not supported in the current version. No implementation for expressions.
    @Override
    public DataType getDataType()
    {
        return data.getType();
    }
    */

    @Override
    public int hashCode()
    {
        return data.hashCode();
    }

    @Override
    public boolean equals(Object obj)
    {
        if (this == obj) return true;
        if (obj == null) return false;

        if (getClass() != obj.getClass())
            return false;

        final NodeValue other = (NodeValue) obj;
        return data.equals(other.data);
    }

    @Override
    public String toString()
    {
        return data.getValue().toString();
    }
}
