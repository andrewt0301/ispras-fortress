/*
 * Copyright (c) 2013 ISPRAS (www.ispras.ru)
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * ExprTreeWalker.java, Dec 17, 2013 11:28:28 AM Andrei Tatarnikov
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

package ru.ispras.fortress.expression;

import ru.ispras.fortress.expression.ExprTreeVisitor.Status;

/**
 * The ExprTreeWalker class provides methods that traverse an expression tree
 * and apply a visitor to its nodes.<pre></pre>
 * 
 * NOTE: Actions taken in the traversal process  depend on the current status
 * of the visitor (see {@link Status}). There are three possible statuses:
 * (1) OK - continue traversal, (2) SKIP - skip child nodes and (3) ABORT -
 * stop traversal. The status is checked after calling any visitor method.
 * Once ABORT is set, all traversal methods return. If after a call to
 * a method having the Begin suffix (e.g. onExprBegin), the SKIP status is set
 * (not ABORT and not OR), nested elements of the visited node (child nodes or
 * subtrees) are not traversed and a corresponding terminating method (that has
 * the End suffix) is called.<pre></pre>
 * 
 * @author Andrei Tatarnikov
 */

public final class ExprTreeWalker
{
    private final ExprTreeVisitor visitor;

    /**
     * Constructs an ExprTreeWalker object.
     * 
     * @param visitor Visitor to be applied to tree nodes.
     * 
     * @throws NullPointerException if the visitor parameter is null.
     */

    public ExprTreeWalker(ExprTreeVisitor visitor)
    {
        if (null == visitor)
            throw new NullPointerException();

        this.visitor = visitor;
    }

    /**
     * Checks whether the current status of the visitor equals
     * the specified status.
     * 
     * @param status Status to be checked for equality with the current status
     * of the visitor.   
     * @return <code>true</code> if the visitor status equals
     * the specified status, or <code>false</code> otherwise.
     */

    private boolean isStatus(Status status)
    {
        return visitor.getStatus() == status;
    }

    /**
     * Visits a sequence of expression trees. Each node in the sequence 
     * is considered a root of an expression tree and the visitor is
     * notified about it by calls to the onRootBegin and onRootEnd methods. 
     * 
     * @param trees A sequence of expression trees to be visited.
     * 
     * @throws NullPointerException if the parameter equals null.
     * IllegalArgumentException if any of the child nodes of the
     * expression nodes in the sequence has a unknown type.
     */

    public void visit(Iterable<Node> trees)
    {
        if (null == trees)
            throw new NullPointerException();

        for (Node tree : trees)
        {
            visit(tree);
            if (isStatus(Status.ABORT)) return; 
        }
    }

    /**
     * Visits the specified expression node. The visited node is considered
     * a root of an expression tree and the visitor is notified about it by
     * calls to the onRootBegin and onRootEnd methods. 
     * 
     * @param tree Expression tree to be visited.
     * 
     * @throws NullPointerException if the parameter equals null.
     * @throws IllegalArgumentException if any of the expression
     * tree nodes has a unknown type.
     */

    public void visit(Node tree)
    {
        if (null == tree)
            throw new NullPointerException();

        visitor.onRootBegin();
        if (isStatus(Status.ABORT)) return;

        if (isStatus(Status.OK))
        {
            visitNode(tree);
            if (isStatus(Status.ABORT)) return;
        }

        visitor.onRootEnd();
    }

    /**
     * Visits the specified node.
     * 
     * @param node Node to be visited.
     * 
     * @throws NullPointerException if the parameter equals null.
     * @throws IllegalArgumentException if the node or any of its child
     * nodes has a unknown type. 
     */

    public void visitNode(Node node)
    {
        if (null == node)
            throw new NullPointerException();

        switch (node.getKind())
        {
        case VALUE:
            visitValue((NodeValue) node);
            break;

        case VARIABLE:
            visitVariable((NodeVariable) node);
            break;

        case EXPR:
            visitExpr((NodeExpr) node);
            break;

        case BINDING:
            visitBinding((NodeBinding) node);
            break;

        default:
            throw new IllegalArgumentException(
                String.format("Unknown node kind: %s.", node.getKind()));
        }
    }

    private void visitExpr(NodeExpr node)
    {
        if (null == node)
            throw new NullPointerException();

        visitor.onExprBegin(node);
        if (isStatus(Status.ABORT)) return;

        if (isStatus(Status.OK))
        {
            for (int index = 0; index < node.getOperandCount(); index++)
            {
                final Node operand = node.getOperand(index);

                visitor.onOperandBegin(node, operand, index);
                if (isStatus(Status.ABORT)) return;

                if (isStatus(Status.OK))
                {
                    visitNode(operand);
                    if (isStatus(Status.ABORT)) return;
                }

                visitor.onOperandEnd(node, operand, index);
                if (isStatus(Status.ABORT)) return;
            }
        }

        visitor.onExprEnd(node);
    }

    private void visitValue(NodeValue node)
    {
        if (null == node)
            throw new NullPointerException();

        visitor.onValue(node);
    }

    private void visitVariable(NodeVariable node)
    {
        if (null == node)
            throw new NullPointerException();

        visitor.onVariable(node);
    }

    private void visitBinding(NodeBinding node)
    {
        if (null == node)
            throw new NullPointerException();

        visitor.onBindingBegin(node);

        for (NodeBinding.BoundVariable bound : node.getBindings())
        {
            visitor.onBoundVariableBegin(node, bound.getVariable(), bound.getValue());
            visitNode(bound.getValue());
            visitor.onBoundVariableEnd(node, bound.getVariable(), bound.getValue());
        }
        visitor.onBindingListEnd(node);

        visitNode(node.getExpression());

        visitor.onBindingEnd(node);
    }
}
