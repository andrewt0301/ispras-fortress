/*
 * Copyright (c) 2013 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * SolverBase.java, Dec 23, 2013 2:32:47 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.solver.constraint.ConstraintKind;
import ru.ispras.fortress.solver.function.Function;

public abstract class SolverBase implements Solver
{
    private static final String ERR_ALREADY_REGISTERED =
        "The %s.%s operation is already registered.";

    private final String                              name;
    private final String                       description;
    private final Set<ConstraintKind>       supportedKinds;
    private final boolean                        isGeneric;
    private final Map<Enum<?>, SolverOperation> operations;

    public SolverBase(
        String name,
        String description,
        Set<ConstraintKind> supportedKinds,
        boolean isGeneric
        )
    {
        notNullCheck(name, "name");
        notNullCheck(description, "description");
        notNullCheck(supportedKinds, "supportedKinds");
        
        this.name           = name;
        this.description    = description;
        this.supportedKinds = supportedKinds;
        this.isGeneric      = isGeneric;
        this.operations     = new HashMap<Enum<?>, SolverOperation>();
    }
    
    private static void notNullCheck(Object o, String name)
    {
        if (null == o)
            throw new NullPointerException(name + " is null");
    }

    @Override
    public final String getName()
    {
        return name;
    }

    @Override
    public final String getDescription()
    {
        return description;
    }

    @Override
    public final boolean isSupported(ConstraintKind kind)
    {
        return supportedKinds.contains(kind);
    }

    @Override
    public final boolean isGeneric()
    {
        return isGeneric;
    }
    
    public final Map<Enum<?>, SolverOperation> getOperations()
    {
        return Collections.unmodifiableMap(operations);
    }

    @Override
    public final boolean addCustomOperation(Enum<?> id, Function function)
    {
        if (null == id)
            throw new NullPointerException();

        if (null == function)
            throw new NullPointerException();

        return null == operations.put(id, SolverOperation.newCustom(id, function));
    }

    protected final void addStandardOperation(StandardOperation id, String text)
    {
        if (null == id)
            throw new NullPointerException();

        if (null == text)
            throw new NullPointerException();

        if (operations.containsKey(id))
        {
            throw new IllegalArgumentException(
                String.format(ERR_ALREADY_REGISTERED, id.getClass().getSimpleName(), id.name()));
        }

        operations.put(id, SolverOperation.newStandard(id, text));
    }
}
