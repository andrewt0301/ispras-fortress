/*
 * Copyright (c) 2013 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * StandardOperationsInt.java, Nov 7, 2013 5:01:29 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.calculator;

import java.util.EnumMap;
import java.util.Map;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataTypeId;
import ru.ispras.fortress.expression.StandardOperation;

/**
 * The StandardOperationsInt enumeration holds a collection of operation objects that are 
 * responsible for performing standard operations (StandardOperation) on data objects that
 * hold integers (DataTypeId.LOGIC_INTEGER).
 * 
 * <pre> 
 * Implementation details and conventions common for all operation groups implemented as enumerations:
 *   
 * 1. The enumeration implements the Operation interface parameterized with the StandardOperation
 * type.
 * 
 * 2. Each operation is represented by an element of the enumeration that provides implementation
 * for the "calculate" methods with one and two parameters. If one of the overloaded "calculate" 
 * method is not applicable for the operation the UnsupportedOperationException runtime exception
 * is thrown.
 * 
 * 3. Each enumeration elements holds operation identifier and the range of the allowed operand number.
 * 
 * 4. The enumeration provides the 'dataTypeId' static method that returns the identifier of
 * the data type for which the enumeration provides operations.
 * </pre>
 * 
 * @author Andrei Tatarnikov
 */

enum StandardOperationsInt implements Operation<StandardOperation>
{
    PLUS (StandardOperation.PLUS, ArityRange.UNARY)
    {
        @Override
        public Data calculate(Data operand)
        {
            return operand;
        }

        @Override
        public Data calculate(Data operand1, Data operand2)
        {
            throw new UnsupportedOperationException();
        }
    },

    MINUS (StandardOperation.MINUS, ArityRange.UNARY)
    {
        @Override
        public Data calculate(Data operand)
        {
            final int value = extractInteger(operand);
            return Data.newInteger(- value);
        }

        @Override
        public Data calculate(Data operand1, Data operand2)
        {
            throw new UnsupportedOperationException();
        }
    },

    ADD (StandardOperation.ADD, ArityRange.BINARY_UNBOUNDED)
    {
        @Override
        public Data calculate(Data operand)
        {
            throw new UnsupportedOperationException();
        }

        @Override
        public Data calculate(Data operand1, Data operand2)
        {
            final int value1 = extractInteger(operand1);
            final int value2 = extractInteger(operand2);

            return Data.newInteger(value1 + value2);
        }
    },

    SUB (StandardOperation.SUB, ArityRange.BINARY_UNBOUNDED)
    {
        @Override
        public Data calculate(Data operand)
        {
            throw new UnsupportedOperationException();
        }

        @Override
        public Data calculate(Data operand1, Data operand2)
        {
            final int value1 = extractInteger(operand1);
            final int value2 = extractInteger(operand2);

            return Data.newInteger(value1 - value2);
        }
    },

    MUL (StandardOperation.MUL, ArityRange.BINARY_UNBOUNDED)
    {
        @Override
        public Data calculate(Data operand)
        {
            throw new UnsupportedOperationException();
        }

        @Override
        public Data calculate(Data operand1, Data operand2)
        {
            final int value1 = extractInteger(operand1);
            final int value2 = extractInteger(operand2);

            return Data.newInteger(value1 * value2);
        }
    },

    DIV (StandardOperation.DIV, ArityRange.BINARY)
    {
        @Override
        public Data calculate(Data operand)
        {
            throw new UnsupportedOperationException();
        }

        @Override
        public Data calculate(Data operand1, Data operand2)
        {
            final int value1 = extractInteger(operand1);
            final int value2 = extractInteger(operand2);

            return Data.newInteger(value1 / value2);
        }
    },

    REM(StandardOperation.REM, ArityRange.BINARY)
    {
        @Override
        public Data calculate(Data operand)
        {
            throw new UnsupportedOperationException();
        }

        @Override
        public Data calculate(Data operand1, Data operand2)
        {
            final int value1 = extractInteger(operand1);
            final int value2 = extractInteger(operand2);

            return Data.newInteger(value1 % value2);
        }
    },

    MOD (StandardOperation.MOD, ArityRange.BINARY)
    {    
        @Override
        public Data calculate(Data operand)
        {
            throw new UnsupportedOperationException();
        }

        @Override
        public Data calculate(Data operand1, Data operand2)
        {
            final int value1 = extractInteger(operand1);
            final int value2 = extractInteger(operand2);

            return Data.newInteger(value1 % value2);
        }
    }
    ;

    private static final Map<StandardOperation, Operation<StandardOperation>> operations;

    static
    {
        operations = new EnumMap<StandardOperation, Operation<StandardOperation>>(StandardOperation.class);

        for (Operation<StandardOperation> value : values())
            operations.put(value.getOperationId(), value);
    }

    public static Map<StandardOperation, Operation<StandardOperation>> operations()
    {
        return operations; 
    }

    private final StandardOperation operationId;
    private final ArityRange        operationArity;

    private StandardOperationsInt(StandardOperation operationId, ArityRange operationArity)
    {
        this.operationId = operationId;
        this.operationArity = operationArity;
    }

    public static DataTypeId dataTypeId()
    {
        return DataTypeId.LOGIC_INTEGER;
    }

    @Override
    public final StandardOperation getOperationId()
    {
        return operationId;
    }

    @Override
    public final ArityRange getOperationArity()
    {
        return operationArity;
    }

    private static int extractInteger(Data data)
    {
        assert data.getType().getValueClass().equals(Integer.class);
        return ((Number) data.getValue()).intValue();
    }
}
