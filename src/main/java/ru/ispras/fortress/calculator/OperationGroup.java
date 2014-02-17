/*
 * Copyright (c) 2013 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * OperationGroup.java, Jun 25, 2013 12:35:42 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.calculator;

import java.util.EnumMap;
import java.util.Map;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.DataTypeId;

/**
 * The OperationGroup class is an implementation of a calculator engine that encapsulates
 * a collection of objects that implement specific operations. Operation objects are
 * grouped by the data type they perform operations on. That is, there may be several
 * implementations of the same operation for different data types. 
 * 
 * @author Andrei Tatarnikov
 * 
 * @param <OperationId> Class of the enumeration that specifies operations included in the operation
 * group. An operation group object can hold only operations that are members of the same group and
 * are described as elements of the same enumeration. 
 */

public final class OperationGroup<OperationId extends Enum<OperationId>> implements CalculatorEngine
{
    // Key - data type identifier, value: [map: key - operation identifier, value - operation object]
    private final Map<DataTypeId, Map<OperationId, Operation<OperationId>>> operations;

    /**
     * Constructor for an operation group object. 
     */

    public OperationGroup()
    {
        this.operations = new EnumMap<DataTypeId, Map<OperationId, Operation<OperationId>>>(DataTypeId.class);
    }

    /**
     * Registers a group of operators that perform calculations on a specific data type.
     * 
     * @param typeId Data type identifier.
     * @param operationsForType A map of operation on the specified data type. Key is the operation 
     * identifier and value is the operation implementation.
     */

    public final void registerOperations(
        DataTypeId typeId, Map<OperationId, Operation<OperationId>> operationsForType)
    {
        assert null != typeId;
        assert null != operationsForType;

        operations.put(typeId, operationsForType);
    }

    /**
     * {@inheritDoc}
     */

    @Override
    public final boolean isSupported(Enum<?> operationId, Data[] operands)
    {
        if ((null == operands) || (0 == operands.length))
            return false;

        if (!equalTypes(operands))
            return false;

        final DataTypeId typeId = operands[0].getType().getTypeId();
        if (!operations.containsKey(typeId))
            return false;

        final Map<OperationId, Operation<OperationId>> operationsForType = operations.get(typeId);
        if (!operationsForType.containsKey(operationId))
            return false;

        final Operation<OperationId> operation = operationsForType.get(operationId);
        if (!operation.getOperandRange().isWithinRange(operands.length))
            return false;

        return true;
    }
    
    /**
     * {@inheritDoc}
     */

    @Override
    public final Data calculate(Enum<?> operationId, Data[] operands)
    {
        if (!isSupported(operationId, operands))
        {
            throw new UnsupportedOperationException(
                String.format(MSG_UNSUPPORTED_FRMT, operationId, operands[0].getType().getTypeId()));
        }

        final DataTypeId typeId = operands[0].getType().getTypeId();
        final Map<OperationId, Operation<OperationId>> operationsForType = operations.get(typeId);

        final Operation<OperationId> operation = operationsForType.get(operationId);
        return calculate(operation, operands);
    }

    /**
     * Checks whether all data objects in the specified array have equal types.
     * This is an invariant: operations require data objects that have equal types. 
     * 
     * @param operands Array of data objects.
     * @return <code>true</code> if all objects have equal types or <code>false</code> otherwise.
     */

    private static boolean equalTypes(Data[] operands)
    {
        if (operands.length <= 1)
            return true;

        final DataType type = operands[0].getType();
        for (int index = 1; index < operands.length; ++index)
        {
            if (!operands[index].getType().equals(type))
                return false;
        }

        return true;
    }

    /**
     * Performs calculation using the specified operation object. Depending on the number
     * of operands it call different methods of operation objects. For unary operations
     * an unary method is called and for binary operations a binary method is called.
     * When the number of operands is greater that two, calculation is performed by
     * calling the binary method sequentially. The result of the previous call is used
     * as the first operand for the second call.   
     * 
     * @param operation Operation object that is responsible for calculations.
     * @param operands Data object array.
     * @return Data object that contains the calculated value.
     */

    private Data calculate(Operation<OperationId> operation, Data[] operands)
    {
        assert operation.getOperandRange().isWithinRange(operands.length);

        if (Range.Bound.UNARY.value() == operands.length)
            return operation.calculate(operands[0]);

        if (Range.Bound.BINARY.value() == operands.length)
            return operation.calculate(operands[0], operands[1]);

        Data result = operation.calculate(operands[0], operands[1]);

        for(int index = 2; index < operands.length; ++index)
            result = operation.calculate(result, operands[index]);

        return result;
    }

    private final String MSG_UNSUPPORTED_FRMT = 
        "Failed to calculate: %s is unsupported for the %s type or operand types are mismatched.";
}
