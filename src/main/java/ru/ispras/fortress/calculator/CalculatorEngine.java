/*
 * Copyright 2013-2014 ISP RAS (http://www.ispras.ru)
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
 * The CalculatorEngine interface is an interface to be implemented by all calculator engines.
 * Calculator engines perform calculations using operations united into a group. Operation groups
 * are represented by corresponding enumerations that list supported operations.
 * 
 * @author Andrei Tatarnikov
 */

public interface CalculatorEngine {
  /**
   * Checks whether the specified operation is supported for the provided operands. Operation
   * identifier and operand types are taken into consideration.
   * 
   * @param operatorId Operator identifier. Identifies an operation within a group.
   * @param operands Array of operands.
   * @return {@code true} if the operation is supported for the given operand types or {@code false}
   *         if it is not supported or its invariants are violated (e.g. operand types do not
   *         match).
   */

  boolean isSupported(Enum<?> operatorId, Data... operands);

  /**
   * Performs calculation by applying the specified operation to the operands.
   * 
   * @param operatorId Operator identifier. Identifies an operation within a group.
   * @param operands Array of operands.
   * @return Data object holding the calculated value.
   * 
   * @throws UnsupportedOperationException if the operation is not supported or its invariants are
   *         violated (e.g. operand types do not match).
   */

  Data calculate(Enum<?> operatorId, Data... operands);
}
