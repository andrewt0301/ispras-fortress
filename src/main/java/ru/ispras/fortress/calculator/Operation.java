/*
 * Copyright (c) 2013 ISPRAS (www.ispras.ru)
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * Operation.java, Nov 6, 2013 2:48:38 PM Andrei Tatarnikov
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

import ru.ispras.fortress.data.Data;

/**
 * The Operation interface is a contract for objects implementing operations 
 * on data objects.
 * 
 * @author Andrei Tatarnikov
 *
 * @param <OperationId> Type of the enumeration that describes a group
 * of operations.
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
     * Performs an operation on the specified operands.  
     * 
     * @param operands A variable of operands. 
     * @return Data object containing the calculated value.
     * 
     * @throws NullPointerException if null is passed to the method.
     * @throws UnsupportedOperationException if the operation
     * requires a number of arguments which is different from the one 
     * passed to the method.
     */

    public Data calculate(Data ... operands);
}
