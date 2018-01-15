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
import ru.ispras.fortress.data.DataTypeId;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.util.InvariantChecks;

import java.util.HashMap;
import java.util.Map;

/**
 * The {@link Calculator} class is responsible for performing calculations on data objects using an
 * extendible set of operations. It encapsulates a table of calculator engines each implementing
 * operations that belong to some logic group. Each group is represented by a enumeration
 * identifying operations it contains. The class of the enumeration is used to identify engines
 * implementing operations from the given group. It is possible to extend functionality by
 * registering custom engines implementing new group of operations. Also, you can replace existing
 * engines with custom engines if needed.
 * 
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public final class Calculator {
  private Calculator() {}

  /**
   * A singleton for the calculator engine that implements standard operations described by the
   * StandardOperation enumeration.
   */
  public static final CalculatorEngine STANDARD;

  // Key: class of the operation group enumeration, value: engine implementing
  // operations from the group.
  private static final Map<Class<? extends Enum<?>>, CalculatorEngine> ENGINES =
      new HashMap<>();

  static {
    // Creates and registers an engine that performs calculation using
    // standard operations.

    final OperationGroup<StandardOperation> standardOperations =
        new OperationGroup<>();

    // Register operation for Bool values.
    standardOperations.registerOperations(StandardOperationsBool.dataTypeId(),
        StandardOperationsBool.operations());

    // Register operation for Int values.
    standardOperations.registerOperations(StandardOperationsInt.dataTypeId(),
        StandardOperationsInt.operations());

    standardOperations.registerOperations(DataTypeId.LOGIC_REAL, StandardOperations.realOps());
    standardOperations.registerOperations(DataTypeId.MAP, StandardOperations.arrayOps());
    standardOperations.registerOperations(DataTypeId.BIT_VECTOR,
                                          StandardOperations.bitVectorOps());

    STANDARD = standardOperations;
    registerEngine(StandardOperation.class, STANDARD);
  }

  /**
   * Registers a calculator engine that performs calculations using operations that belong to the
   * given operation group which is described with a corresponding enumeration. The class of the
   * enumeration serves as a key.
   * 
   * @param operationIdClass Class of the enumeration that identifies operations implemented by the
   *        given calculator engine.
   * @param engine Calculator engine to be registered.
   * @return <code>true</code> if the engine was successfully registered and it had not been
   *         previously registered or <code>false</code> if an engine identified by the specified
   *         class had already been registered (in this case, it is replaced with a new engine).
   * 
   * @throws IllegalArgumentException if any of the parameters equals {@code null}.
   */

  public static boolean registerEngine(
        final Class<? extends Enum<?>> operationIdClass,
        final CalculatorEngine engine) {
    InvariantChecks.checkNotNull(operationIdClass);
    InvariantChecks.checkNotNull(engine);

    return null == ENGINES.put(operationIdClass, engine);
  }

  /**
   * Returns the engine that performs calculations using a specific group of operations. Operations
   * that belong to a single group are identified with a corresponding enumeration. The class of the
   * enumeration serves as a key. If no such engine is registered <code>null</code> is returned.
   * 
   * @param operationIdClass Class of the enumeration that identifies operations implemented by the
   *        given engine.
   * @return Engine responsible for performing a specific group of operations or <code>null</code>
   *         if no such engine is registered.
   * 
   * @throws IllegalArgumentException if the parameter equals {@code null}.
   */
  public static CalculatorEngine getEngine(final Class<?> operationIdClass) {
    InvariantChecks.checkNotNull(operationIdClass);
    return ENGINES.get(operationIdClass);
  }

  /**
   * Checks whether the specified operation is supported for the provided operands. The class of the
   * operation identifier, its value and operand types are taken into consideration.
   * 
   * @param operationId Operation identifier. Identifies an operation within a group.
   * @param operands A variable number of operands.
   * @return <code>true</code> if the operation is supported for the given operand types or
   *         <code>false</code> otherwise.
   * 
   * @throws IllegalArgumentException if any of the parameters equals {@code null}.
   */
  public static boolean isSupported(final Enum<?> operationId, final Data... operands) {
    InvariantChecks.checkNotNull(operationId);
    InvariantChecks.checkNotNull(operands);

    final CalculatorEngine engine = getEngine(operationId.getClass());
    if (null == engine) {
      return false;
    }

    return engine.isSupported(operationId, operands);
  }

  /**
   * Performs calculation by applying the specified engine and operation to the operands.
   * 
   * @param engine Calculator engine.
   * @param operationId Operation identifier. Identifies an operation within a group.
   * @param operands A variable number of operands.
   * @return Data object holding the calculated value.
   * 
   * @throws IllegalArgumentException if any of the parameters equals {@code null}.
   * @throws UnsupportedOperationException if the operation is not supported or its invariants are
   *         violated (e.g. operand types do not match).
   */
  public static Data calculate(
      final CalculatorEngine engine,
      final Enum<?> operationId,
      final Data... operands) {
    InvariantChecks.checkNotNull(engine);
    InvariantChecks.checkNotNull(operationId);
    InvariantChecks.checkNotNull(operands);

    return engine.calculate(operationId, operands);
  }

  /**
   * Performs calculation by applying the specified operation to the operands.
   * 
   * @param operationId Operation identifier. Identifies an operation within a group.
   * @param operands A variable number of operands.
   * @return Data object holding the calculated value.
   * 
   * @throws IllegalArgumentException if any of the parameters equals {@code null}.
   * @throws UnsupportedOperationException if the operation is not supported or its invariants are
   *         violated (e.g. operand types do not match).
   */
  public static Data calculate(final Enum<?> operationId, final Data... operands) {
    InvariantChecks.checkNotNull(operationId);
    InvariantChecks.checkNotNull(operands);

    final CalculatorEngine engine = getEngine(operationId.getClass());
    if (null == engine) {
      throw new UnsupportedOperationException(
          String.format(MSG_UNSUPPORTED_GROUP_FRMT, operationId.getClass().getSimpleName()));
    }

    return engine.calculate(operationId, operands);
  }

  private static final String MSG_UNSUPPORTED_GROUP_FRMT =
      "The specified operation family is not supported: %s.";
}
