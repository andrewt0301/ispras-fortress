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
import ru.ispras.fortress.solver.function.FunctionTemplate;

/**
 * The SolverOperation class stores information about a solver operation.
 * The information explains how the operation should be translated to
 * solver-specific representation. The SolverOperation class describes
 * both built-in and custom solver operation.
 *
 * @author Andrei Tatarnikov
 */

public abstract class SolverOperation
{
    /**
     * Describes the type of the solver operation.
     * 
     * @author Andrei Tatarnikov
     */

    public static enum Kind
    {
        TEXT,
        FUNCTION,
        TEMPLATE
    }

    private final Kind   kind;
    private final Enum<?>  id;

    public static final SolverOperation newText(Enum<?> id, String text)
    {
        if (null == id)
            throw new NullPointerException();
        
        if (text == null)
            throw new NullPointerException();
        
       return new TextOperation(id, text); 
        
    }

    public static final SolverOperation newFunction(Function function)
    {
        if (null == function)
            throw new NullPointerException();

        return new FunctionOperation(function);
    }
    
    public static final SolverOperation newTemplate(FunctionTemplate template)
    {
        if (null == template)
            throw new NullPointerException();
        
        return new TemplateOperation(template); 
    }

    /**
     * Creates a solver operation object (a custom operation).
     * @param text Textual representation of the operation.
     * @param function Definition of the operation (including its parameters and underlying expression).
     */

    private SolverOperation(Kind kind, Enum<?> id)
    {
        this.kind = kind;
        this.id   = id;
    }

    /**
     * Returns information of the type of the operation.
     * 
     * @return Operation kind.
     */

    public final Kind getKind()
    {
        return kind;
    }

    /**
     * Returns the textual representation of the operation.
     * @return Textual representation of the operation.
     */

    public final Enum<?> getOperationId()
    {
        return id;
    }

    public abstract String getText();

    /**
     * Returns the underlying function.
     * @return Underlying function.
     */

    public abstract Function getFunction();

    /**
     * Returns the underlying function template.
     * @return Underlying function template.
     */

    public abstract FunctionTemplate getTemplate();
    
    private static class TextOperation extends SolverOperation
    {
        private final String text;

        private TextOperation(Enum<?> id, String text)
        {
            super(Kind.TEXT, id);
            this.text = text;
        }

        @Override
        public String getText() { return text; }

        @Override
        public Function getFunction() { return null; }

        @Override
        public FunctionTemplate getTemplate() { return null; }
    }
    
    private static class FunctionOperation extends SolverOperation
    {
        private final Function function;

        private FunctionOperation(Function function)
        {
            super(Kind.FUNCTION, function.getId());
            this.function = function;
        }

        @Override
        public String getText() { return function.getUniqueName(); }

        @Override
        public Function getFunction() { return function; }

        @Override
        public FunctionTemplate getTemplate() { return null; }
    }

    private static class TemplateOperation extends SolverOperation
    {
        private final FunctionTemplate template;

        private TemplateOperation(FunctionTemplate template)
        {
            super(Kind.TEMPLATE, template.getId());
            this.template = template;
        }

        @Override
        public String getText() { return null; }

        @Override
        public Function getFunction() { return null; }

        @Override
        public FunctionTemplate getTemplate() { return template; }
    }
}
