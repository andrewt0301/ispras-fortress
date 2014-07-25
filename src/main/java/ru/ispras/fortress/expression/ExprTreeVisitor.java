/*
 * Copyright (c) 2013 ISPRAS (www.ispras.ru)
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * ExprTreeVisitor.java, Dec 17, 2013 12:32:29 PM Andrei Tatarnikov
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

/**
 * Interface to be implemented by all visitor objects applied to an expression
 * tree to collect information or to build another representation of the expression.   
 * 
 * @author Andrei Tatarnikov
 */

public interface ExprTreeVisitor
{
    /**
     * Notifies that processing of an expression tree has been started.
     */

    void onRootBegin();

    /**
     * Notifies that processing of an expression tree has been finished. 
     */

    void onRootEnd();

    /**
     * Starts visiting an expression node.
     * 
     * @param expr Expression node.
     */

    void onExprBegin(NodeExpr expr);

    /**
     * Finishes visiting an expression node.
     * 
     * @param expr Expression node.
     */

    void onExprEnd(NodeExpr expr);

    /**
     * Notifies that visiting an expression operand has started. 
     * 
     * @param expr Expression node.
     * @param operand Operand node.
     * @param index Operand index.
     */

    void onOperandBegin(NodeExpr expr, Node operand, int index);

    /**
     * Notifies that visiting an expression operand has finished.
     * 
     * @param expr Expression node.
     * @param operand Operand node.
     * @param index Operand index.
     */

    void onOperandEnd(NodeExpr expr, Node operand, int index);

    /**
     * Notifies that a value node has been visited. 
     * 
     * @param value Value node.
     */

    void onValue(NodeValue value);

    /**
     * Notifies that a variable node has been visited.
     * 
     * @param variable Variable node.
     */

    void onVariable(NodeVariable variable);
}
