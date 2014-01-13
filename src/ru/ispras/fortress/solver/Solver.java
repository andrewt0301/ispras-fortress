/*
 * Copyright (c) 2011 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * Solver.java, Dec 20, 2011 12:18:10 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver;

import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintKind;
import ru.ispras.fortress.solver.function.Function;

/**
 * The Solver interface provides a protocol for working with different kinds
 * of constraint solvers in a universal way.
 * 
 * @author Andrei Tatarnikov
 */

public interface Solver
{
    /**
     * Returns the name of the solver. 
     * 
     * @return Solver name.
     */

    public String getName();

    /**
     * Returns the description of the solver. 
     * 
     * @return solver description.
     */

    public String getDescription();

    /**
     * Check whether the specified constraint kind is supported by the solver.  
     * 
     * @param kind Constraint kind.
     * @return true if the constraint kind is supported or false otherwise. 
     */

    public boolean isSupported(ConstraintKind kind); 
    
    /**
     * Returns true if the solver is generic and false if it is custom.
     * 
     * @return true for generic solvers or false for custom ones.
     */

    public boolean isGeneric();

    /**
     * Solves the specified constraint.
     * 
     * @param constraint A constraint object.
     * @return Result of solving the constraint.
     */

    public SolverResult solve(Constraint constraint);

    /**
     * Register a custom operation that extends the functionality of the 
     * solver. The operation is implemented in terms of existing operation
     * and represents a function.
     * 
     * @param function Object describing the semantics and syntax of the operation.
     */

    public boolean addCustomOperation(Enum<?> id, Function function);
}
