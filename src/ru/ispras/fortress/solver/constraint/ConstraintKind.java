/*
 * Copyright (c) 2013 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * ConstraintKind.java, Dec 13, 2013 11:07:36 AM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver.constraint;

import ru.ispras.fortress.solver.SolverId;

/**
 * The ConstraintKind enumeration describes constraint types.
 *  
 * @author Andrei Tatarnikov
 */

public enum ConstraintKind
{
    /**
     * Constant based on formula expressions (described by the Formula class and solved by the Z3_TEXT solver).
     */

    FORMULA_BASED(Formulas.class, SolverId.Z3_TEXT);

    private final Class<?>    innerRepClass;
    private final SolverId defaultSolverId;

    /**
     * Construct a ConstraintKind object basing on provided information.
     * 
     * @param innerRepClass Class that stores internal representation of constraints of the given type.
     * @param defaultSolverId Identifier of a solver to be used by default for constraints of the given type.
     */

    private ConstraintKind(Class<?> innerRepClass, SolverId defaultSolverId)
    {
        this.innerRepClass = innerRepClass;
        this.defaultSolverId = defaultSolverId;
    }

    /**
     * Returns the class used to describe internal representation of constraints of the given type.
     * 
     * @return Constraint internal representation class.
     */

    public Class<?> getInnerRepClass()
    {
        return innerRepClass;
    }

    /**
     * Returns the identifier of the solver that should be used to solve constraints of the given type by default. 
     * 
     * @return Solver identifier.
     */

    public SolverId getDefaultSolverId()
    {
        return defaultSolverId;
    }
}
