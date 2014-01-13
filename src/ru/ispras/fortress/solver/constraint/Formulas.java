/*
 * Copyright (c) 2011 ISPRAS
 *
 * Institute for System Programming of Russian Academy of Sciences
 *
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 *
 * All rights reserved.
 *
 * Formulas.java, Dec 20, 2011 12:24:24 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver.constraint;

import java.util.ArrayList;
import java.util.List;

import ru.ispras.fortress.expression.NodeExpr;

/**
 * The Formulas class serves as a container for formula expressions (assertions)
 * that specify the invariants for a taken constraint
 *
 * @author Andrei Tatarnikov
 */

public final class Formulas
{
    private final List<NodeExpr> formulas;

    public Formulas()
    {
        this.formulas = new ArrayList<NodeExpr>();
    }

    public Formulas(Formulas formulas)
    {
        if (null == formulas)
            throw new NullPointerException();

        this.formulas = new ArrayList<NodeExpr>(formulas.formulas);
    }

    /**
     * Adds a new formula expression to the collection
     * 
     * @param formula A formula expression
     */
    
    public void add(NodeExpr formula)
    {
        if (null == formula)
            throw new NullPointerException();

        formulas.add(formula);
    }

    public void addAll(Iterable<NodeExpr> formulas)
    {
        if (null == formulas)
            throw new NullPointerException();

        for (NodeExpr formula : formulas)
            add(formula);
    }

    public void addAll(Formulas formulas)
    {
        if (null == formulas)
            throw new NullPointerException();

        addAll(formulas.exprs());
    }

    /**
     * Provides access to the collection of formula expressions
     * 
     * @return Iterable for the collection of formula expressions
     */

    public Iterable<NodeExpr> exprs()
    {
        return formulas;
    }
    
    public NodeExpr asSingleExpr()
    {
        NodeExpr root = null;

        for (NodeExpr item : exprs())
            root = (null == root) ? item : NodeExpr.AND(root, item); 

        return root;
    }

    @Override
    public int hashCode()
    {
        return formulas.hashCode();
    }

    @Override
    public boolean equals(Object obj)
    {
        if (this == obj) return true;
        if (obj == null) return false;

        if (getClass() != obj.getClass())
            return false;

        final Formulas other = (Formulas) obj;

        if (!formulas.equals(other.formulas))
            return false;

        return true;
    }

    @Override
    public String toString()
    {
        return formulas.toString();
    }
}
