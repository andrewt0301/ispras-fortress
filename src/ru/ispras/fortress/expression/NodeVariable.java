/*
 * Copyright (c) 2011 ISPRAS
 *
 * Institute for System Programming of Russian Academy of Sciences
 *
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 *
 * All rights reserved.
 *
 * NodeVariable.java, Dec 20, 2011 12:23:34 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.expression;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.Variable;

/**
 * The NodeVariable class represents a node that refers to a variable which is specified
 * as an attribute of a constraint. The class serves as an adapter to allow Variable objects
 * to be used in an expression tree. The variable is unknown or has a value.
 *
 * @author Andrei Tatarnikov
 */

public final class NodeVariable extends Node
{
    private final Variable variable;

    /**
     * Creates a node based on a Variable object.
     * 
     * @param variable A variable node object.
     */

    public NodeVariable(Variable variable)
    {
        super(Kind.VARIABLE);

        if (null == variable)
            throw new NullPointerException();

        this.variable = variable;
    }

    /**
     * Returns the name of the variable.
     * 
     * @return The variable name.
     */

    public String getName()
    {
        return variable.getName();
    }

    /**
     * Returns the data object that encapsulates the variable value.
     * 
     * @return A data object.
     */

    public Data getData()
    {
        return variable.getData();
    }

    /**
     * Returns an object that stores a data value if any value was assigned to the variable 
     * (it is a known variable) or null if it is an unknown variable. The exact type of
     * the object returned by the method depends on the implementation. Please see 
     * the {@link ru.ispras.fortress.data.DataTypeId} enumeration for details on internal
     * representation of data objects
     * 
     * @return Object that stores the variable value if it is assigned or null otherwise
     */

    public Object getValue()
    {
        return variable.getData().getValue();
    }

    /* TODO: Not supported in the current version. No implementation for expressions.
    @Override
    public DataType getDataType()
    {
        return variable.getData().getType();
    }
    */

    @Override
    public int hashCode()
    {
        return variable.hashCode();
    }

    @Override
    public boolean equals(Object obj)
    {
        if (this == obj) return true;
        if (obj == null) return false;

        if (getClass() != obj.getClass())
            return false;

        final NodeVariable other = (NodeVariable) obj;
        return variable.equals(other.variable);
    }

    @Override
    public String toString()
    {
        return (variable.hasValue()) ?
            variable.getData().getValue().toString() : variable.getName();
    }
}
