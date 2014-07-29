/*
 * Copyright (c) 2013 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * ConstraintBuilder.java, Nov 13, 2013 3:07:12 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver.constraint;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.UUID;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;

/**
 * The ConstraintBuilder class is a builder that creates Constraint objects.
 * 
 * @author Andrei Tatarnikov
 */

public final class ConstraintBuilder
{
    private String                           name;
    private String                    description;
    private ConstraintKind                   kind;
    private final Map<String, Variable> variables;
    private Object                 representation;

    /**
     * Constructs a ConstraintBuilder object with default values.
     * 
     * Default name is a pseudo random UUID (see java.util.UUID.randomUUID()).
     * Default description is an empty string.
     * Default constraint type is formula-based (ConstraintKind.FORMULA_BASED).
     */

    public ConstraintBuilder()
    {
        this(ConstraintKind.FORMULA_BASED);
    }

    /**
     * Constructs a ConstraintBuilder object using the provided constraint type.
     * 
     * Default name is a pseudo random UUID (see java.util.UUID.randomUUID()).
     * Default description is an empty string.
     * 
     * @param kind Constraint type.
     * 
     * @throws NullPointerException if the parameter equals null.
     */

    public ConstraintBuilder(ConstraintKind kind)
    {
        if (null == kind)
            throw new NullPointerException();

        this.name           = UUID.randomUUID().toString();
        this.description    = "";
        this.kind           = kind;
        this.variables      = new LinkedHashMap<String, Variable>();
        this.representation = null;
    }

    /**
     * Constructs a ConstraintBuilder object object using information
     * from an existing Constraint object.
     * 
     * @param constraint An existing constraint.
     * 
     * @throws NullPointerException if the parameter is null.
     */

    public ConstraintBuilder(Constraint constraint)
    {
        if (null == constraint)
            throw new NullPointerException();

        this.name           = constraint.getName();
        this.kind           = constraint.getKind();
        this.description    = constraint.getDescription();
        this.variables      = createVariableMap(constraint.getVariables());
        this.representation = constraint.getInnerRep();
    }

    private static Map<String, Variable> createVariableMap(Iterable<Variable> variables)
    {
        final Map<String, Variable> result = new LinkedHashMap<String, Variable>();

        for (Variable v : variables)
            result.put(v.getName(), v);

        return result;
    }

    /**
     * Sets the name of the constraint to be created.
     * 
     * @param name Constraint name.
     * 
     * @throws NullPointerException if the parameter equals null.
     */

    public void setName(String name)
    {
        if (null == name)
            throw new NullPointerException();

        this.name = name;
    }
    
    /**
     * Sets the description of the constraint to be created.
     * 
     * @param description Constraint description.
     * 
     * @throws NullPointerException if the parameter equals null.
     */

    public void setDescription(String description)
    {
        if (null == description)
            throw new NullPointerException();

        this.description = description;
    }

    /**
     * Sets the type of the constraint to be created.
     * 
     * @param kind Constraint type.
     * 
     * @throws NullPointerException if the parameter equals null.
     */

    public void setKind(ConstraintKind kind)
    {
        if (null == kind)
            throw new NullPointerException();

        this.kind = kind;
    }

    /**
     * Sets the internal representation of the constraint to be created.
     * 
     * @param value Internal representation of the constraint.
     * 
     * @throws NullPointerException if the parameter equals null.
     */

    public void setInnerRep(Object value)
    {
        if (null == value)
            throw new NullPointerException();

        this.representation = value;
    }

    /**
     * Adds variables in the specified collection to the constraint to be created.
     * Variables are added directly (no copies are created).
     * 
     * @param variables A collection of variables.
     * 
     * @throws NullPointerException if the parameter equals null.
     * @throws IllegalArgumentException if the specified variable name has already been
     * use to define a variable that has different type or value (an illegal attempt to
     * redefine the variable). See the internal addVariable method.
     */

    public void addVariables(Iterable<Variable> variables)
    {
        if (null == variables)
            throw new NullPointerException();
        
        for (Variable variable : variables)
            addVariable(variable);
    }

    /**
     * Adds copies of variables in the specified collection to the constraint to be created.
     * 
     * @param variables A collection of variables.
     * 
     * @throws NullPointerException if the parameter equals null.
     * @throws IllegalArgumentException if the specified variable name has already been
     * use to define a variable that has different type or value (an illegal attempt to
     * redefine the variable). See the internal addVariable method. 
     */

    public void addVariableCopies(Iterable<Variable> variables)
    {
        if (null == variables)
            throw new NullPointerException();

        for (Variable variable : variables)
            addVariable(variable.getName(), variable.getData());
    }
    
    /**
     * Creates a variable that has the specified name and type, adds it to
     * the constraint to be created and returns a reference to it.  
     * 
     * @param name Variable name.
     * @param type Variable type.
     * @return A reference to the created variable.
     * 
     * @throws NullPointerException if any of the parameters equals null.
     * @throws IllegalArgumentException if the specified variable name has already been
     * use to define a variable that has different type or value (an illegal attempt to
     * redefine the variable). See the internal addVariable method. 
     */

    public Variable addVariable(String name, DataType type)
    {
        if (null == name)
            throw new NullPointerException();
        
        if (null == type)
            throw new NullPointerException();

        return addVariable(new Variable(name, type));
    }
    
    /**
     * Creates a variable that has the specified name and type, adds it to
     * the constraint to be created and returns a reference to it. 
     * 
     * @param name Variable name.
     * @param data Data object that specifies the type and the value of the variable.
     * @return A reference to the created variable.
     * 
     * @throws NullPointerException if any of the parameters equals null.
     * @throws IllegalArgumentException if the specified variable name has already been
     * use to define a variable that has different type or value (an illegal attempt to
     * redefine the variable). See the internal addVariable method. 
     */

    public Variable addVariable(String name, Data data)
    {
        if (null == name)
            throw new NullPointerException();

        if (null == data)
            throw new NullPointerException();

        return addVariable(new Variable(name, data));
    }

    /**
     * Note: internal method. Adds the specified variable to the constraint to be
     * created and returns a reference to it. If such a variable has already been
     * added (a variable with equal name and value is present in the variable table)
     * the new variable is ignored and the method returns a reference to an existing
     * one. If the existing variable has a different type or value, it is considered
     * as an illegal attempt to redefine the variable and an exception is thrown.   
     * 
     * @param variable Variable object.
     * @return A referent to the variable in the variable table.
     * 
     * @throws NullPointerException if the parameter equals null.
     * @throws IllegalArgumentException if the specified variable name has already been
     * use to define a variable that has different type or value (an illegal attempt to
     * redefine the variable). 
     */

    private Variable addVariable(Variable variable)
    {
        if (null == variable)
            throw new NullPointerException();

        if (!variables.containsKey(variable.getName()))
        {
            variables.put(variable.getName(), variable);
            return variable;
        }

        final Variable oldVariable = variables.get(variable.getName());
        if (!oldVariable.equals(variable))
        {
            throw new IllegalArgumentException(
                String.format(ILLEGAL_VARIABLE_REDEFINITION, variable.getName()));
        }

        // When equal, the new variable is ignored.
        return oldVariable;
    }

    /**
     * Builds the Constraint object basing on the specified attributes and returns it.
     * 
     * @return A new constraint.
     * 
     * @throws NullPointerException see the invariants of the Constraint class constructor.
     * @throws IllegalArgumentException see the invariants of the Constraint class constructor.
     */

    public Constraint build()
    {
        return new Constraint(name, kind, description, variables, representation); 
    }

    private final String ILLEGAL_VARIABLE_REDEFINITION =
        "Illegal attempt to redefine the existing variable %s with a different type or value."; 
}
