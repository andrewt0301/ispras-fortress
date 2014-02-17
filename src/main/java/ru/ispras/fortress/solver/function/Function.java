/*
 * Copyright (c) 2012 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * Function.java, Oct 3, 2012 4:27:10 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver.function;


import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.Node;

/**
 * The Function class describes a custom function that extends the functionality
 * of a solver. A function represents an operation described in terms of
 * expressions that use existing solver operations.
 * 
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */

public final class Function
{
    private final DataType   returnType;
    private final Node       body;
    private final Variable[] parameters;

    /**
     * Creates a function with a variable number of parameters.
     * 
     * @param returnType The function return type.
     * @param body The body of the function (underlying expression).
     * @param parameters An variable-length list of parameters.
     * 
     * @throws NullPointerException if any of the method parameters equals null.
     */

    public Function(DataType returnType, Node body, Variable ... parameters)
    {
        if (null == returnType)
            throw new NullPointerException();

        if (null == body)
            throw new NullPointerException();

        if (null == parameters)
            throw new NullPointerException();

        this.returnType = returnType;
        this.body       = body;
        this.parameters = parameters;
    }

    /**
     * Returns the function return type.
     * 
     * @return The function return type.
     */

    public DataType getReturnType()
    {
        return returnType;
    }

    /**
     * Returns the body of the function (underlying expression).
     * 
     * @return The syntax element describing the body of the function.
     */

    public Node getBody()
    {
        return body;
    }

    /**
     * Returns the parameter count.
     * 
     * @return The number of parameters.
     */

    public int getParameterCount()
    {
        return parameters.length;
    }

    /**
     * Returns function parameters by their index.
     * 
     * @param index The index of the needed parameter.
     * @return A function parameter.
     * 
     * @throws IndexOutOfBoundsException if the parameter index is out of bounds of the parameter array.
     */

    public Variable getParameter(int index)
    {
        if (!((0 <= index) && (index < parameters.length)))
            throw new IndexOutOfBoundsException();

        return parameters[index];
    }
}
