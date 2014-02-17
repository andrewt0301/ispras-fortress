/*
 * Copyright (c) 2013 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * SolverResultBuilder.java, Dec 20, 2013 2:09:21 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver;

import java.util.ArrayList;
import java.util.List;

import ru.ispras.fortress.data.Variable;

public final class SolverResultBuilder
{
    private SolverResult.Status status; 
    private List<String>        errors;
    private List<Variable>   variables;

    /**
     * Constructs a SolverResultBuilder object.
     * 
     * @param status The initial status of the result.
     */

    public SolverResultBuilder(SolverResult.Status status)
    {
        if (null == status)
            throw new NullPointerException();

        this.status     = status;
        this.errors     = new ArrayList<String>();
        this.variables  = new ArrayList<Variable>();
    }

    /**
     * Creates a solver result object basing attributes hold by the builder. 
     * 
     * @return A new solver result object.
     */

    public SolverResult build()
    {
        return new SolverResult(status, errors, variables);
    }

    /**
     * Sets the status of the result.
     * 
     * @param status Result status.
     */

    public void setStatus(SolverResult.Status status)
    {
        this.status = status;
    }

    /**
     * Adds an error description to the list of errors.
     * 
     * @param error An error description.
     */

    public void addError(String error)
    {
        errors.add(error);
    }

    /**
     * Adds a variable to the list of variables.
     * 
     * @param variable A variable object.
     */

    public void addVariable(Variable variable)
    {
        variables.add(variable);
    }
}
