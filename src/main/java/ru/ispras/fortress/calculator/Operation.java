/*
 * Copyright (c) 2013 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * Operation.java, Nov 6, 2013 2:48:38 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.calculator;

import ru.ispras.fortress.data.Data;

/**
 * The Operation interface is a contract for objects implementing operations on data objects.
 * 
 * @author Andrei Tatarnikov
 *
 * @param <OperationId> Type of the enumeration that describes a group of operations.
 */

public interface Operation<OperationId extends Enum<OperationId>>
{
    /**
     * Returns the identifier of the operation.
     * 
     * @return Operation identifier.
     */

    public OperationId getOperationId();

    /**
     * Returns the range that describes the allowed arity of the operation.  
     * 
     * @return Range of operation arity.
     */

    public ArityRange getOperationArity();

    /**
     * Performs an unary operation on the specified operand. If the current operation
     * requires a number of arguments other than one (it is not an unary operation),
     * the UnsupportedOperationException runtime exception should be thrown.  
     * 
     * @param operand Operand data object. 
     * @return Data object containing the calculated value.
     */

    public Data calculate(Data operand);

    /**
     * Performs a binary operation on the specified operand. If the current operation
     * requires a number of arguments other than two (it is not a binary operation),
     * the UnsupportedOperationException runtime exception should be thrown.  
     * 
     * @param operand1 Left operand data object. 
     * @param operand2 Right operand data object.
     * @return Data object containing the calculated value.
     */

    public Data calculate(Data operand1, Data operand2);
}
