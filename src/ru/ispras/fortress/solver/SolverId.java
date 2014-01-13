/*
 * Copyright (c) 2012 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * SolverId.java, Jan 13, 2012 4:37:14 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver;

import ru.ispras.fortress.solver.engine.z3.Z3TextSolver;

/**
 * The SolverId enumeration specifies which solver should be used
 * to solve a particular constraint. 
 *  
 * @author Andrei Tatarnikov
 */

public enum SolverId 
{
    /**
     * Z3 solver by Microsoft Research. It processes a text file with 
     * SMT-LIB code and prints results to the output stream.
     */

    Z3_TEXT
    {
        protected Solver createSolver() { return new Z3TextSolver(); }
    },

    /**
     * The solver which is used by default. Currently, it is Z3_TEXT.
     */

    DEFAULT
    {
        protected Solver createSolver() { return new Z3TextSolver(); }
    };

    private Solver solver = null;

    public final Solver getSolver()
    {
        if (null == solver)
            solver = createSolver();
        
        return solver;
    }

    protected abstract Solver createSolver();
}
