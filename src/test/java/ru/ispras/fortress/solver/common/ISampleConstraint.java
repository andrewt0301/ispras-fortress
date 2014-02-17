/*
 * Copyright (c) 2012 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * ISampleConstraint.java, Oct 4, 2012 12:40:18 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver.common;

import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.solver.constraint.Constraint;

public interface ISampleConstraint
{
    public Constraint getConstraint();
    public Iterable<Variable> getExpectedVariables();
}
