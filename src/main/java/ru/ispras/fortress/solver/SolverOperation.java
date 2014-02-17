/*
 * Copyright (c) 2012 ISPRAS
 *
 * Institute for System Programming of Russian Academy of Sciences
 *
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 *
 * All rights reserved.
 *
 * SolverOperation.java, Oct 2, 2012 11:30:06 AM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver;

import ru.ispras.fortress.solver.function.Function;

/**
 * The SolverOperation class stores information about a solver operation.
 * The information explains how the operation should be translated to
 * solver-specific representation. The SolverOperation class describes
 * both built-in and custom solver operation.
 *
 * @author Andrei Tatarnikov
 */

public final class SolverOperation
{
    private final Enum<?>  id;
    private final String   text;
    private final Function function;
    
    public static final SolverOperation newStandard(Enum<?> id, String text)
    {
        if (null == id)
            throw new NullPointerException();
        
        if (text == null)
            throw new NullPointerException();

        return new SolverOperation(id, text, null);
    }
    
    public static final SolverOperation newCustom(Enum<?> id, Function function)
    {
        if (null == id)
            throw new NullPointerException();

        if (null == function)
            throw new NullPointerException();

        return new SolverOperation(id, id.name(), function);
    }

    /**
     * Creates a solver operation object (a custom operation).
     * @param text Textual representation of the operation.
     * @param function Definition of the operation (including its parameters and underlying expression).
     */

    private SolverOperation(Enum<?> id, String text, Function function)
    {
        this.id       = id;
        this.text     = text;
        this.function = function;
    }

    /**
     * Returns the textual representation of the operation.
     * @return Textual representation of the operation.
     */
    
    public Enum<?> getOperationId()
    {
        return id;
    }

    public String getText()
    {
        return text;
    }

    /**
     * Returns the underlying function of a custom operation.
     * @return Underlying function of a custom operation.
     */

    public Function getFunction()
    {
        return function;
    }

    /**
     * Return a flag that indicates whether the operation is custom or not.
     * @return true for custom operations and false for built-in operations.
     */

    public boolean isCustom()
    {
        return function != null;
    }
}
