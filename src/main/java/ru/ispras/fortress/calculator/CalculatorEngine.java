/*
 * Copyright (c) 2013 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * CalculatorEngine.java, Jun 24, 2013 11:25:44 AM Andrei Tatarnikov
 */

package ru.ispras.fortress.calculator;

import ru.ispras.fortress.data.Data;

/**
 * The CalculatorEngine interface is an interface to be implemented by calculator engines.
 * Calculator engines perform calculations using operations united into a group. Operation
 * groups are represented by corresponding enumerations that list supported operations.
 * 
 * @author Andrei Tatarnikov
 */

public interface CalculatorEngine
{
    /**
     * Checks whether the specified operation is supported for the provided operands.
     * Operation identifier and operand types are taken into consideration.
     * 
     * @param operatorId Operator identifier. Identifies an operation within a group.
     * @param operands Array of operands.
     * @return <code>true</code> if the operation is supported for the given operand
     * types or <code>false</code> if it is not supported or its invariants are violated
     * (e.g. operand types do not match). 
     */

    public boolean isSupported(Enum<?> operatorId, Data[] operands);

    /**
     * Performs calculation by applying the specified operation to the operands. If the operation
     * is not supported or its invariants are violated (e.g. operand types do not match) 
     * the UnsupportedOperationException runtime exception will be thrown.
     * 
     * @param operatorId Operator identifier. Identifies an operation within a group.
     * @param operands Array of operands.
     * @return Data object holding the calculated value.
     */

    public Data calculate(Enum<?> operatorId, Data[] operands);
}
