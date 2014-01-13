/*
 * Copyright (c) 2012 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * SolverResult.java, May 4, 2012 10:46:47 AM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver;

import java.util.List;

import ru.ispras.fortress.data.Variable;

/**
 * The SolverResult class stores a solution to the specified constraint
 * including the status of the operation and the list of errors if any occurred.
 * 
 * @author Andrei Tatarnikov
 */

public final class SolverResult
{
    /**
     * Describes possible statuses of the results produced by a constraint solver.
     * 
     * @author Andrei Tatarnikov
     */

    public static enum Status
    {
        SAT,
        UNSAT,
        UNKNOWN,
        ERROR
    }

    private final Status            status; 
    private final List<String>      errors;
    private final List<Variable> variables;

    /**
     * Constructs for a solver result object basing on specified attributes.
     * 
     * @param status Status of the result.
     * @param errors List of errors.
     * @param variables List of variables.
     * 
     * @throws NullPointerException if any of the parameters equals null.
     */

    public SolverResult(
        Status status,
        List<String> errors,
        List<Variable> variables
        )
    {
        if (null == status)
            throw new NullPointerException();

        if (null == errors)
            throw new NullPointerException();

        if (null == variables)
            throw new NullPointerException();

        this.status     = status;
        this.errors     = errors;
        this.variables  = variables;
    }

    /** 
     * Returns the status of the result.
     * 
     * @return Solver result status.  
     */

    public Status getStatus()
    {
        return status;
    }

    /**
     * Checks whether any errors were detected during the process of solving a constraint.        
     * 
     * @return true if any errors were detected or false otherwise.  
     */

    public boolean hasErrors()
    {
        return !errors.isEmpty(); 
    }

    /**
     * Returns the lists of errors that occurred during the process of solving a constraint.
     * 
     * @return An iterator for the list of errors. 
     */

    public Iterable<String> getErrors()
    {
        return errors;
    }

    /**
     * Returns an iterator for the collection of variables that
     * store a solution to a constraint.
     * 
     * @return An iterator for the collection of output variables.  
     */

    public Iterable<Variable> getVariables()
    {
        return variables;
    }
}
