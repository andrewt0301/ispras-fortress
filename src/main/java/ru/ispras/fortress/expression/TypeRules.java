/*
 * Copyright (c) 2014 ISPRAS (www.ispras.ru)
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * OperationRules.java, Jul 31, 2014 12:21:02 PM Andrei Tatarnikov
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

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.DataTypeId;

enum TypeRules implements TypeRule
{
    UNKNOWN
    {
        @Override
        public DataType getResultType(DataType[] operandTypes)
        {
            return DataType.UNKNOWN;
        }
    },

    BOOLEAN
    {
        @Override
        public DataType getResultType(DataType[] operandTypes)
        {
            return DataType.BOOLEAN;
        }
    },

    BIT_BOOLEAN
    {
        @Override
        public DataType getResultType(DataType[] operandTypes)
        {
            return DataType.BIT_VECTOR(1);
        }
    },

    FIRST_KNOWN_BV_ARG
    {
        @Override
        public DataType getResultType(DataType[] operandTypes)
        {
            DataType result = DataType.UNKNOWN;

            for (DataType dataType : operandTypes)
            {
                if (dataType.getTypeId() == DataTypeId.BIT_VECTOR)
                {
                    result = dataType;
                    break;
                }
            }

            return result;
        }
    },
    
    SECOND_VB_ARG
    {
        @Override
        public DataType getResultType(DataType[] operandTypes)
        {
            if (operandTypes.length > 1 &&
                operandTypes[1].getTypeId() == DataTypeId.BIT_VECTOR)
            {
                return operandTypes[1];
            }

            return DataType.UNKNOWN;
        }
    },

    FIRST_NUM_ARG
    {
        @Override
        public DataType getResultType(DataType[] operandTypes)
        {
            if (operandTypes.length > 0)
            {
                if (operandTypes[0].getTypeId() == DataTypeId.LOGIC_INTEGER ||
                    operandTypes[0].getTypeId() == DataTypeId.LOGIC_REAL)
                {
                    return operandTypes[0];
                }
            }

            return DataType.UNKNOWN;
        }
    },

    FIRST_KNOWN_NUM_ARG
    {
        @Override
        public DataType getResultType(DataType[] operandTypes)
        {
            DataType result = DataType.UNKNOWN;

            for (DataType dataType : operandTypes)
            {
                if (dataType.getTypeId() == DataTypeId.LOGIC_INTEGER ||
                    dataType.getTypeId() == DataTypeId.LOGIC_REAL) 
                {
                    result = dataType;
                    break;
                }
            }

            return result;
        }
    },
    
    ITE
    {
        @Override
        public DataType getResultType(DataType[] operandTypes)
        {
            if (operandTypes.length > 2)
            {
                if (operandTypes[1].getTypeId() != DataTypeId.UNKNOWN)
                    return operandTypes[1]; 
            
                if (operandTypes[2].getTypeId() != DataTypeId.UNKNOWN)
                    return operandTypes[2];
            }

            return DataType.UNKNOWN;
        }
    }
}
