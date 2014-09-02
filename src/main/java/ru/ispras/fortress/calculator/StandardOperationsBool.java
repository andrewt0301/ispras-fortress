/*
 * Copyright (c) 2014 ISPRAS (www.ispras.ru) 
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * StandardOperationsBool.java, Sep 2, 2014 8:07:15 AM Alexander Kamkin
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

package ru.ispras.fortress.calculator;

import java.util.EnumMap;
import java.util.Map;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataTypeId;
import ru.ispras.fortress.expression.StandardOperation;

/**
 * The StandardOperationsBool enumeration holds a collection of operation
 * objects that are responsible for performing standard operations
 * (StandardOperation) on data objects that hold booleans
 * (DataTypeId.LOGIC_BOOLEAN).<pre></pre>
 *  
 * Implementation details and conventions common for all operation groups
 * implemented as enumerations:<pre></pre>
 *   
 * 1. The enumeration implements the Operation interface parameterized with
 * the StandardOperation type.<pre></pre>
 * 
 * 2. Each operation is represented by an element of the enumeration that
 * provides implementation for the "calculate" methods with one and two
 * parameters. If one of the overloaded "calculate" method is not applicable
 * for the operation the UnsupportedOperationException runtime exception
 * is thrown.<pre></pre>
 * 
 * 3. Each enumeration elements holds operation identifier and the range
 * of the allowed operand number.<pre></pre>
 * 
 * 4. The enumeration provides the "dataTypeId" static method that returns
 * the identifier of the data type for which the enumeration provides
 * operations.<pre></pre>
 *  
 * @author Andrei Tatarnikov
 */

enum StandardOperationsBool implements Operation<StandardOperation>
{
    NOT (StandardOperation.NOT, ArityRange.UNARY)
    {
        @Override
        public Data calculate(Data ... operands)
        {
            return Data.newBoolean(!extractBoolean(operands[0]));
        }
    },

    AND (StandardOperation.AND, ArityRange.BINARY_UNBOUNDED)
    {
        @Override
        public Data calculate(Data ... operands)
        {
            for(int index = 0; index < operands.length; ++index)
            {
                if(!extractBoolean(operands[index]))
                    return Data.newBoolean(false);
            }

            return Data.newBoolean(true);
        }
    },

    OR (StandardOperation.OR, ArityRange.BINARY_UNBOUNDED)
    {
        @Override
        public Data calculate(Data ... operands)
        {
            for(int index = 0; index < operands.length; ++index)
            {
                if(extractBoolean(operands[index]))
                    return Data.newBoolean(true);
            }

            return Data.newBoolean(false);
        }
    },

    XOR (StandardOperation.XOR, ArityRange.BINARY_UNBOUNDED)
    {
        @Override
        public Data calculate(Data ... operands)
        {
            boolean result = extractBoolean(operands[0]);

            for(int index = 1; index < operands.length; ++index)
                result ^= extractBoolean(operands[index]);

            return Data.newBoolean(result);
        }
    },

    IMPL (StandardOperation.IMPL, ArityRange.BINARY)
    {
        @Override
        public Data calculate(Data ...operands)
        {
            final boolean value1 = extractBoolean(operands[0]);
            final boolean value2 = extractBoolean(operands[1]);

            return Data.newBoolean(!value1 || value2);
        }
    }
    ;

    private static final Map<StandardOperation, Operation<StandardOperation>> operations;

    static
    {
        operations = new EnumMap<
            StandardOperation, Operation<StandardOperation>>(StandardOperation.class);

        for (Operation<StandardOperation> value : values())
            operations.put(value.getOperationId(), value);
    }

    public static Map<StandardOperation, Operation<StandardOperation>> operations()
    {
        return operations; 
    }

    private final StandardOperation operationId;
    private final ArityRange        operationArity;

    private StandardOperationsBool(
        StandardOperation operationId,
        ArityRange operationArity
        )
    {
        this.operationId    = operationId;
        this.operationArity = operationArity;
    }

    public static DataTypeId dataTypeId()
    {
        return DataTypeId.LOGIC_BOOLEAN;
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

    private static boolean extractBoolean(Data data)
    {
        assert data.getType().getValueClass().equals(Boolean.class);
        return ((Boolean) data.getValue()).booleanValue();
    }
}
