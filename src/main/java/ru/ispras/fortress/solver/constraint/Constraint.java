/*
 * Copyright (c) 2012 ISPRAS
 *
 * Institute for System Programming of Russian Academy of Sciences
 *
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 *
 * All rights reserved.
 *
 * Constraint.java, Jan 11, 2012 4:56:25 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver.constraint;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.Variable;

/**
 * The Constraint class stores a description of a constraint and provides facilities
 * to perform manipulations with it. The Constraint class allows describing various
 * constraint types. Depending on the constraint type (described by the kind field),
 * its internal representation (see the representation field) can use a different class
 * to store the information.
 *
 * @authors Andrei Tatarnikov, Sergey Smolov
 */

public final class Constraint
{
    private final String                     name;
    private final ConstraintKind             kind;
    private final String              description;
    private final Map<String, Variable> variables;
    private final Object           representation;

    /**
     * Constructs a <code>Constraint</code> object.
     * 
     * @param name Constraint name (uniquely identifies the constraint).
     * @param kind Constraint type (gives information about its internal representation format).
     * @param description Constraint description.
     * @param variables Table of constraint variables.
     * @param representation Description of the constraint internals (internal representation)
     * in a format that depends on the type of the constraint.
     * 
     * @throws NullPointerException if any of the parameters equals null.
     * @throws IllegalArgumentException (1) if the internal representation class does not match
     * the class required by the constraint type; (2) if the table of variables is empty.  
     */

    public Constraint(
        String                     name,
        ConstraintKind             kind,
        String              description,
        Map<String, Variable> variables,
        Object           representation
        )
    {
        notNullCheck(name,                     "name");
        notNullCheck(kind,                     "kind");
        notNullCheck(description,       "description");
        notNullCheck(variables,           "variables");
        notNullCheck(representation, "representation");

        if (representation.getClass() != kind.getInnerRepClass())
        {
            throw new IllegalArgumentException(
                String.format(ILLEGAL_IR_CLASS,
                    representation.getClass().getName(), kind.getInnerRepClass().getName()));
        }

        if (variables.isEmpty())
        {
            throw new IllegalArgumentException(EMPTY_VARIABLES);
        }

        this.name           = name;
        this.description    = description;
        this.kind           = kind;
        this.variables      = variables;
        this.representation = representation;
    }

    private static void notNullCheck(Object o, String name)
    {
        if (null == o)
            throw new NullPointerException(name + " is null");
    }

    /**
     * Returns the name that uniquely identifies a constraint.
     * 
     * @return Name identifier for the constraint
     */

    public String getName()
    {
        return name;
    }

    /**
     * Returns information on the constraint type (including the format of its internals).
     * 
     * @return Constraint type information.
     */

    public ConstraintKind getKind()
    {
        return kind;
    }

    /**
     * Returns the description of the constraint (some additional information).
     * 
     * @return Textual description of the constraint.
     */

    public String getDescription()
    {
        return description;
    }

    /**
     * Returns an object that holds internal description of the constraint. The exact type
     * of the object depends on the constraint type.
     * 
     * @return Internal representation of the constraint.
     */

    public Object getInnerRep()
    {
        return representation;
    }

    /**
     * Assigns a value to a constraint variable (makes it an input variable).
     * 
     * @param name The name of the variable.
     * @param value The data object that stores the variable value.
     * 
     * @throws NullPointerException if any of the parameters equals null.
     * @throws IllegalArgumentException (1) if a variable with such name is not defined;
     * (2) if the value type does not match the type of the variable.
     */

    public void setVariableValue(String name, Data value)
    {
        notNullCheck(name,   "name");
        notNullCheck(value, "value");

        if (!variables.containsKey(name))
        {
            throw new IllegalArgumentException(
                String.format(UNDEFINED_VARIABLE, name));
        }

        final Variable variable = variables.get(name);
        if (!variable.getData().getType().equals(value.getType()))
        {
            throw new IllegalArgumentException(
                String.format(ILLEGAL_TYPE, variable.getData().getType(), value.getType()));
        }

        variable.setData(value);
    }

    /**
     * Finds a constraint variable by its name. If no such variable is found, null is returned.
     *
     * @param name The name of the variable to be searched for.
     * @return variable Variable object or null if the variable is not defined.
     * 
     * @throws NullPointerException if the name parameter equals null.
     */

    public Variable findVariable(String name)
    {
        notNullCheck(name, "name");
        return variables.get(name);
    }

    /**
     * Returns an Iterable object that provides an iterator for the collection of constraint variables.
     *
     * @return variables An Iterable object to access constraint variables. 
     */

    public Iterable<Variable> getVariables()
    {
        return variables.values();
    }

    /**
     * Returns an Iterable object to access unknown constraint variables (that have no assigned value).
     * 
     * @return An Iterable object to access constraint variables.
     */

    public Iterable<Variable> getUnknownVariables()
    {
        final List<Variable> result = new ArrayList<Variable>(variables.size());

        for (Variable variable : variables.values())
        {
            if (!variable.hasValue())
                result.add(variable);
        }

        return result;
    }

    @Override
    public int hashCode()
    {
        final int prime = 31;
        int result = 1;

        result = prime * result + name.hashCode();
        result = prime * result + kind.hashCode();
        result = prime * result + variables.hashCode();
        result = prime * result + representation.hashCode();

        return result;
    }

    @Override
    public boolean equals(Object obj)
    {
        if (this == obj) return true;
        if (obj == null) return false;

        if (getClass() != obj.getClass())
            return false;

        final Constraint other = (Constraint) obj;

        if (!name.equals(other.name))
            return false;

        if (kind != other.kind)
            return false;

        if (!variables.equals(other.variables))
            return false;

        if (null == representation)
            return representation == other.representation;

        return representation.equals(other.representation);
    }

    @Override
    public String toString()
    {
        return representation.toString();
    }

    private static final String UNDEFINED_VARIABLE = "%s is illegal variable name. No such varaible is defined.";
    private static final String       ILLEGAL_TYPE = "%s is illegal data type, %s is expected.";
    private static final String   ILLEGAL_IR_CLASS = "%s is illegal representation class, %s is expected.";
    private static final String    EMPTY_VARIABLES = "The variable table is empty.";
}