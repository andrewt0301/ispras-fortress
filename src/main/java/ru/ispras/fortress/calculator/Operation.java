/*
 * Copyright 2013-2018 ISP RAS (http://www.ispras.ru)
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software distributed under the License
 * is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
 * or implied. See the License for the specific language governing permissions and limitations under
 * the License.
 */

package ru.ispras.fortress.calculator;

import ru.ispras.fortress.data.Data;

/**
 * The {@link Operation} interface is a contract for objects implementing
 * operations on data objects.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 *
 * @param <OperationIdT> Type of the enumeration that describes a group of operations.
 */
public interface Operation<OperationIdT extends Enum<OperationIdT>> {
  /**
   * Returns the identifier of the operation.
   *
   * @return Operation identifier.
   */
  OperationIdT getOperationId();

  /**
   * Returns the range that describes the allowed arity of the operation.
   *
   * @return Range of operation arity.
   */
  ArityRange getOperationArity();

  /**
   * Performs an operation on the specified operands.
   *
   * @param operands A variable array of operands.
   * @return Data object containing the calculated value.
   *
   * @throws IllegalArgumentException if {@code null} is passed to the method.
   * @throws UnsupportedOperationException if the operation requires a number of arguments which is
   *         different from the one passed to the method.
   */
  Data calculate(Data... operands);

  /**
   * Performs type check on the specified operands.
   *
   * @param operands A variable array of operands.
   * @return {@code true} if operand types are valid for the operation or {@code false} otherwise.
   */
  boolean validTypes(Data... operands);
}
