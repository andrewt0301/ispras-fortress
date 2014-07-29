/*
 * Copyright (c) 2011 ISPRAS (www.ispras.ru)
 *
 * Institute for System Programming of Russian Academy of Sciences
 *
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 *
 * All rights reserved.
 *
 * Formulas.java, Dec 20, 2011 12:24:24 PM Andrei Tatarnikov
 * 
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not
 * use this file except in compliance with the License. You may obtain a copy of
 * the License at
 * 
 * http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations under
 * the License.
 */

package ru.ispras.fortress.solver.constraint;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.ExprTreeVisitor;
import ru.ispras.fortress.expression.ExprTreeWalker;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeExpr;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;

/**
 * The Formulas class serves as a container for formula expressions
 * (assertions) that specify the invariants for a taken constraint.
 *
 * @author Andrei Tatarnikov
 */

public final class Formulas
{
    private final List<Node> exprs;

    /**
     * Constructs an empty formula container.
     */

    public Formulas()
    {
        this.exprs = new ArrayList<Node>();
    }

    /**
     * Constructs a new formula container by copying the contents
     * of an existing one.
     * 
     * @param formulas Existing formula container.
     * 
     * @throws NullPointerException if the parameter equals null.
     */

    public Formulas(Formulas formulas)
    {
        if (null == formulas)
            throw new NullPointerException();

        this.exprs = new ArrayList<Node>(formulas.exprs);
    }

    /**
     * Constructs a container than contains the specified formula.
     * 
     * @param formula A formula to be placed in the container.
     */

    public Formulas(Node formula)
    {
        this();
        add(formula);
    }

    /**
     * Adds a formula expression to the formula container.
     * 
     * @param formula A formula expression.
     * 
     * @throws NullPointerException if the parameter equals null.
     */

    public void add(Node formula)
    {
        if (null == formula)
            throw new NullPointerException();

        exprs.add(formula);
    }

    /**
     * Adds all formula expression from the specified collection
     * to the formula container.
     * 
     * @param formulas A collection of formula expressions.
     * 
     * @throws NullPointerException if the parameter equals null.
     */

    public void addAll(Iterable<Node> formulas)
    {
        if (null == formulas)
            throw new NullPointerException();

        for (Node formula : formulas)
            add(formula);
    }

    /**
     * Adds all formula expressions from the specified formula
     * container to the current formula container.
     * 
     * @param formulas Formula container to be copied.
     * 
     * @throws NullPointerException if the parameter equals null.
     */

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

    public Iterable<Node> exprs()
    {
        return exprs;
    }

    /**
     * Unites all stored formula expressions into a single expression
     * using the AND operator and returns it to the client.
     * 
     * @return A single expression for all stored formula expressions.
     */

    public Node asSingleExpr()
    {
        Node root = null;

        for (Node item : exprs())
            root = (null == root) ? item : Node.AND(root, item); 

        return root;
    }

    /**
     * Finds all variables used in the stored formula expressions
     * and returns them to the client.
     * 
     * @return A collection of all variables used in the stored
     * formula expressions.
     * 
     * @throws IllegalStateException if the method finds nodes
     * that refer to different variable instances that have the
     * same name. This is illegal because all variables used
     * in formula expression of a constraint must be accessible
     * via its variable table (the signature of the constraint). 
     */

    public Iterable<Variable> getVariables()
    {
        final Map<String, Variable> variables = 
            new HashMap<String, Variable>();

        final ExprTreeWalker walker = new ExprTreeWalker(new ExprTreeVisitor()
        {
            private static final String ERR_MULTIPLE_VARS = 
               "References to different variables that have the same name %s.";

            @Override
            public void onVariable(NodeVariable variable)
            {
                if (null == variable)
                    throw new NullPointerException();

                if (variables.containsKey(variable.getName()))
                {
                    final Variable existingVariable =
                        variables.get(variable.getName());

                    if (variable.getVariable() != existingVariable)
                        throw new IllegalStateException(String.format(
                            ERR_MULTIPLE_VARS, variable.getName()));
                }
                else
                {
                    variables.put(
                        variable.getName(), variable.getVariable());
                }
            }

            @Override public void onValue(NodeValue value) {}
            @Override public void onRootEnd() {}
            @Override public void onRootBegin() {}
            @Override public void onOperandEnd(NodeExpr expr, Node operand, int index) {}
            @Override public void onOperandBegin(NodeExpr expr, Node operand, int index) {}
            @Override public void onExprEnd(NodeExpr expr) {}
            @Override public void onExprBegin(NodeExpr expr) {}
        });

        walker.visit(exprs());
        return variables.values();
    }

    @Override
    public int hashCode()
    {
        return exprs.hashCode();
    }

    @Override
    public boolean equals(Object obj)
    {
        if (this == obj) return true;
        if (obj == null) return false;

        if (getClass() != obj.getClass())
            return false;

        final Formulas other = (Formulas) obj;

        if (!exprs.equals(other.exprs))
            return false;

        return true;
    }

    @Override
    public String toString()
    {
        return exprs.toString();
    }
}
