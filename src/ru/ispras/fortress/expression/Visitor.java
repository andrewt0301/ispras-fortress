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

import ru.ispras.fortress.data.Data;

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
     * @param op Identifier of the operation used by the expression.
     * @param operands Number of expression operands.
     */

    void onExprBegin(Enum<?> op, int operands);

    /**
     * Finishes visiting an expression node.
     * 
     * @param op Identifier of the operation used by the expression.
     * @param operands Number of expression operands.
     */

    void onExprEnd(Enum<?> op, int operands);

    /**
     * Notifies that visiting an expression operand has started. 
     * 
     * @param op Operation identifier.
     * @param operand Operand node.
     * @param index Operand index.
     */

    void onOperandBegin(Enum<?> op, Node operand, int index);

    /**
     * Notifies that visiting an expression operand has finished.
     * 
     * @param op Operation identifier.
     * @param operand Operand node.
     * @param index Operand index.
     */

    void onOperandEnd(Enum<?> op, Node operand, int index);

    /**
     * Notifies that a value node has been visited. 
     * 
     * @param data Data associated with the node.
     */

    void onValue(Data data);

    /**
     * Notifies that a variable node has been visited.
     * 
     * @param name Variable name.
     * @param data Variable type and value description. 
     */

    void onVariable(String name, Data data);
}
