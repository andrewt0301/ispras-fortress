/*
 * Copyright (c) 2013 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * Visitor.java, Dec 17, 2013 12:32:29 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.expression;

/**
 * Interface to be implemented by all visitor objects applied to an expression
 * tree to collect information or to build another representation of the expression.   
 * 
 * @author Andrei Tatarnikov
 */

public interface Visitor
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
     * @param op Expression node.
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
