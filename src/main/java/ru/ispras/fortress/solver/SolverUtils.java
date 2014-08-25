/*
 * Copyright (c) 2014 ISPRAS (www.ispras.ru)
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * SolverUtils.java, Aug 22, 2014 2:36:30 PM Andrei Tatarnikov
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

package ru.ispras.fortress.solver;

import java.util.Deque;
import java.util.EnumSet;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.expression.ExprTreeVisitor;
import ru.ispras.fortress.expression.ExprTreeVisitor.Status;
import ru.ispras.fortress.expression.ExprTreeVisitorDefault;
import ru.ispras.fortress.expression.ExprTreeWalker;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeBinding;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintBuilder;
import ru.ispras.fortress.solver.constraint.ConstraintKind;
import ru.ispras.fortress.solver.constraint.Formulas;

/**
 * The SolverUtils class provides utility methods to work with
 * logical expressions.
 * 
 * @author Andrei Tatarnikov
 */

public final class SolverUtils
{
    private SolverUtils() {}

    /**
     * Checks whether the specified expression is a logical expression
     * (can be evaluated to boolean).
     * 
     * @param expr Expression to be checked.
     * @return <code>true</code> if the expression is logical (can be evaluated
     * to boolean) or <code>false</code> otherwise.
     * 
     * @throws NullPointerException if the parameter is <code>null</code>.
     */

    public static boolean isCondition(Node expr)
    {
        if (null == expr)
            throw new NullPointerException();

        return expr.getDataType().equals(DataType.BOOLEAN);
    }

    /**
     * Checks whether the specified expression is an atomic logical
     * expression (can be evaluated to boolean and does not include
     * logical operations to combine expressions such as:
     * AND, OR, NOT, XOR and IMPL).
     * 
     * @param expr Expression to be checked.
     * @return <code>true</code> if the expression is an atomic logical
     * expression or <code>false</code> otherwise.
     * 
     * @throws NullPointerException if the parameter is <code>null</code>.
     */

    public static boolean isAtomicCondition(Node expr)
    {
        if (!isCondition(expr))
            return false;

        final Set<StandardOperation> logicOperations = EnumSet.of(
            StandardOperation.AND,
            StandardOperation.OR,
            StandardOperation.NOT,
            StandardOperation.XOR,
            StandardOperation.IMPL
        );

        final ExprTreeVisitor visitor = new ExprTreeVisitorDefault()
        {
            @Override public void onOperationBegin(NodeOperation node)
            {
                if (logicOperations.contains(node.getOperationId()))
                    setStatus(Status.ABORT);
            }
        };

        final ExprTreeWalker walker = new ExprTreeWalker(visitor);
        walker.visit(expr);

        return visitor.getStatus() == Status.OK;
    }

    /**
     * Checks whether the specified expression tree contains bindings
     * (nodes of type BINDING). 
     * 
     * @param expr Expression to be checked.
     * @return <code>true</code> if the expression tree contains bindings
     * (nodes of type BINDING) or <code>false</code> otherwise.
     * 
     * @throws NullPointerException if the parameter is <code>null</code>.
     */

    public static boolean hasBindings(Node expr)
    {
        if (null == expr)
            throw new NullPointerException();

        final ExprTreeVisitor visitor = new ExprTreeVisitorDefault()
        {
            @Override public void onBindingBegin(NodeBinding node)
            {
                setStatus(Status.ABORT);
            }
        };

        final ExprTreeWalker walker = new ExprTreeWalker(visitor);
        walker.visit(expr);

        return visitor.getStatus() == Status.ABORT;
    }

    /**
     * Checks whether the given expression is a constant expression
     * (can be evaluated to a constant value). An expression is considered
     * constant as long as it does not contain unassigned variables
     * (bindings are taken into consideration).
     * 
     * @param expr Expression to be checked.
     * @return <code>true</code> if the expression is a constant expression
     * or <code>false</code> otherwise.
     * 
     * @throws NullPointerException if the parameter is <code>null</code>.
     */

    public static boolean isConstant(Node expr)
    {
        if (null == expr)
            throw new NullPointerException();

        final ExprTreeVisitor visitor = new ExprTreeVisitorDefault()
        {
            // Variables bound to constant values (a stack of scopes).
            private final Deque<Set<String>> knownVariables =
                new LinkedList<Set<String>>();

            @Override public void onVariable(NodeVariable variable)
            {
                if (variable.getVariable().hasValue())
                    return;

                for (Set<String> scope : knownVariables)
                {
                    if (scope.contains(variable.getName()))
                        return;
                }

                setStatus(Status.ABORT);
            }

            @Override public void onBindingBegin(NodeBinding node)
            {
                knownVariables.push(new HashSet<String>());
            }

            @Override public void onBindingEnd(NodeBinding node)
            {
                knownVariables.pop();
            }
   
            @Override public void onBoundVariableEnd(
                NodeBinding node, NodeVariable variable, Node value)
            {
                final Set<String> currentScope = knownVariables.peek();
                currentScope.add(variable.getName());
            }
        };

        final ExprTreeWalker walker = new ExprTreeWalker(visitor);
        walker.visit(expr);

        return visitor.getStatus() == Status.OK;
    }

    /**
     * Performs logical conjunction <code>(exprs[0] && ... && exprs[n-1])
     * </code> of the specified expressions and returns the resulting
     * expression.
     * 
     * @param exprs Expressions to be combined.
     * @return A logical conjunction of the specified expressions.
     * 
     * @throws IllegalArgumentException if no arguments are provided;
     * if an argument is not a logical expression.
     * @throws NullPointerException if any argument in the array is
     * <code>null</code>.
     */

    public static Node getConjunction(Node ... exprs)
    {
        checkNotEmpty(exprs);
        checkAllConditions(exprs);

        return new NodeOperation(StandardOperation.AND, exprs);
    }

    /**
     * Performs logical disjunction <code>(exprs[0] || ... || exprs[n-1])
     * </code> of the specified expressions and returns the resulting
     * expression.
     * 
     * @param exprs Expressions to be combined.
     * @return A logical disjunction of the specified expressions.
     * 
     * @throws IllegalArgumentException if no arguments are provided;
     * if an argument is not a logical expression.
     * @throws NullPointerException if any argument in the array is
     * <code>null</code>.
     */

    public static Node getDisjunction(Node ... exprs)
    {
        checkNotEmpty(exprs);
        checkAllConditions(exprs);

        return new NodeOperation(StandardOperation.OR, exprs);
    }

    /**
     * Performs logical negation <code>(!getConjunction(exprs[0], ..., exprs[n-1]))
     * </code> of the specified expressions combined with conjunction and returns
     * the resulting expression. 
     * 
     * @param exprs Expressions to be combined. 
     * @return A logical negation of the specified expressions.
     * 
     * @throws IllegalArgumentException if no arguments are provided;
     * if an argument is not a logical expression.
     * @throws NullPointerException if any argument in the array is
     * <code>null</code>.
     */

    public static Node getNegation(Node ... exprs)
    {
        return new NodeOperation(StandardOperation.NOT, getConjunction(exprs));
    }

    /**
     * Performs logical complement (negation) 
     * <code>!(getDisjunction(exprs[0], ..., exprs[n-1])</code>
     * of the specified expressions combined with disjunction and returns
     * the resulting expression.
     * 
     * @param exprs Expressions to be combined. 
     * @return A logical complement of the specified expressions.
     * 
     * @throws IllegalArgumentException if no arguments are provided;
     * if an argument is not a logical expression.
     * @throws NullPointerException if any argument in the array is
     * <code>null</code>.
     */

    public static Node getComplement(Node ... exprs)
    {
        return new NodeOperation(StandardOperation.NOT, getDisjunction(exprs));
    }

    /**
     * Checks whether the specified logical conditions are complete
     * <code>!(getComplement(exprs[0], ..., exprs[n-1]) is SAT)</code>.
     * N.B. The method uses the default constraint solver to perform the check. 
     * 
     * @param exprs Conditions (logical expressions) to be checked.
     * @return <code>true</code> if the conditions are complete or
     * <code>false</code> otherwise.
     * 
     * @throws IllegalArgumentException if no arguments are provided;
     * if an argument is not a logical expression.
     * @throws NullPointerException if any argument in the array is
     * <code>null</code>.
     */

    public static boolean areComplete(Node ... exprs)
    {
        final Node target = getComplement(exprs);

        return !isSAT(target);
    }

    /**
     * Checks whether the specified logical conditions are compatible
     * <code>(getConjunction(exprs[0], ..., exprs[n-1]) is SAT)</code>.
     * N.B. The method uses the default constraint solver to perform the check. 
     * 
     * @param exprs Conditions (logical expressions) to be checked. 
     * @return <code>true</code> if the conditions are compatible or
     * <code>false</code> otherwise. 
     * 
     * @throws IllegalArgumentException if no arguments are provided;
     * if an argument is not a logical expression.
     * @throws NullPointerException if any argument in the array is
     * <code>null</code>.
     */

    public static boolean areCompatible(Node ... exprs)
    {
        final Node target = getConjunction(exprs);

        return isSAT(target);
    }

    private static boolean isSAT(Node assertion)
    {
        final ConstraintBuilder builder = 
            new ConstraintBuilder(ConstraintKind.FORMULA_BASED);

        final Formulas formulas = new Formulas(assertion);
        builder.setInnerRep(formulas);

        builder.addVariables(formulas.getVariables());
        final Constraint constraint = builder.build();

        final Solver solver = constraint.getKind().getDefaultSolverId().getSolver();
        final SolverResult solverResult = solver.solve(constraint);

        return SolverResult.Status.SAT == solverResult.getStatus();
    }

    private static void checkNotEmpty(Node ... exprs)
    {
        if (0 == exprs.length)
            throw new IllegalArgumentException("No expressions are provided.");
    }

    private static void checkAllConditions(Node ... exprs)
    {
        for (Node expr : exprs)
            if (!isCondition(expr))
                throw new IllegalArgumentException(
                     "Expression is not a condition: " + expr.toString());
    }
}
