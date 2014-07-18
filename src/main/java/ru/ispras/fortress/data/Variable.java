/*
 * Copyright (c) 2012 ISPRAS
 *
 * Institute for System Programming of Russian Academy of Sciences
 *
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 *
 * All rights reserved.
 *
 * Variable.java, May 5, 2012 3:19:07 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.data;

import javax.xml.bind.annotation.adapters.XmlJavaTypeAdapter;

import ru.ispras.fortress.jaxb.JaxbVariableAdapter;

/**
 * The Variable class describes a variable that can be used as input
 * or output data in constraints. 
 * 
 * @author Andrei Tatarnikov
 */

@XmlJavaTypeAdapter(JaxbVariableAdapter.class)
public final class Variable
{
    private final String name;
    private       Data   data;

    /**
     * Constructs a variable from its name and associated data.
     *
     * @param name Variable name.
     * @param data Data the variable refers to.
     */

    public Variable(String name, Data data)
    {
        if (null == name)
            throw new NullPointerException();

        if (null == data)
            throw new NullPointerException();

        this.name = name;
        this.data = data;
    }

    /**
     * Constructs an uninitialized variable of the specified type. The constructed
     * variable does not refer to any data and its value is set to null.
     * 
     * @param name Variable name.
     * @param type Variable type.
     */

    public Variable(String name, DataType type)
    {
        this(name, type != null ? type.valueUninitialized() : null);
    }

    /**
     * Constructs a full copy of the given variable object. The fields are
     * copied by reference because their types are immutable.
     * 
     * @param variable Variable object to be copied.
     */

    public Variable(Variable variable)
    {
        this(
           variable != null ? variable.name : null,
           variable != null ? variable.data : null
        );
    }

    /**
     * Assigns a new data value to the variable. The data type must be the same.
     *
     * @param data A data value to be assigned to the variable.
     */

    public void setData(Data data)
    {
        if (null == data)
            throw new NullPointerException();

        if (!this.data.getType().equals(data.getType()))
            throw new IllegalArgumentException(
                String.format("%s is illegal data type, %s is expected.", this.data.getType(), data.getType())); 

        this.data = data;
    }

    /**
     * Returns the name of the variable.
     * @return A string representing the variable name.
     */

    public String getName()
    {
        return name;
    }

    /**
     * Returns a data object associated with the specified variable. 
     * @return An IData object associated with the variable.
     */

    public Data getData()
    {
        return data;
    }

    /**
     * Checks whether the variable has a value assigned to it.
     * 
     * @return <code>true</code> if the variable has a value assigned or <code>false</code> otherwise.
     */

    public boolean hasValue()
    {
        return data.hasValue();
    }

    @Override
    public int hashCode()
    {
        final int prime = 31;
        return prime * name.hashCode() + data.hashCode();
    }

    @Override
    public boolean equals(Object obj)
    {
        if (this == obj) return true;
        if (obj == null) return false;

        if (getClass() != obj.getClass())
            return false;

        final Variable other = (Variable) obj;

        if (!name.equals(other.name))
            return false;

        return data.equals(other.data);
    }

    @Override
    public String toString()
    {
        return String.format("Variable[name=%s, data=%s]", name, data); 
    }
}
