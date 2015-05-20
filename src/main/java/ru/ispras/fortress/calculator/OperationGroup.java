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

import static ru.ispras.fortress.util.InvariantChecks.checkNotNull;

import java.util.Collection;
import java.util.EnumMap;
import java.util.Map;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.DataTypeId;
import ru.ispras.fortress.expression.StandardOperation;

/**
 * The OperationGroup class is an implementation of a calculator engine that encapsulates a
 * collection of objects that implement specific operations. Operation objects are grouped by the
 * data type they perform operations on. That is, there may be several implementations of the same
 * operation for different data types.
 * 
 * @author Andrei Tatarnikov
 * 
 * @param <OperationId> Class of the enumeration that specifies operations included in the operation
 *        group. An operation group object can hold only operations that are members of the same
 *        group and are described as elements of the same enumeration.
 */

public final class OperationGroup<OperationId extends Enum<OperationId>>
    implements CalculatorEngine {
  // Key - data type identifier,
  // Value - [map: key - operation identifier, value - operation object]
  private final Map<DataTypeId, Map<OperationId, Operation<OperationId>>> operations;

  /**
   * Constructor for an operation group object.
   */

  public OperationGroup() {
    this.operations =
        new EnumMap<DataTypeId, Map<OperationId, Operation<OperationId>>>(DataTypeId.class);
  }

  /**
   * Registers a group of operators that perform calculations on a specific data type.
   * 
   * @param typeId Data type identifier.
   * @param operationsForType A map of operation on the specified data type. Key is the operation
   *        identifier and value is the operation implementation.
   * 
   * @throws IllegalArgumentException if any of the parameters equals {@code null}.
   */

  public final void registerOperations(
      final DataTypeId typeId,
      final Map<OperationId, Operation<OperationId>> operationsForType) {
    checkNotNull(typeId);
    checkNotNull(operationsForType);

    operations.put(typeId, operationsForType);
  }

  /**
   * {@inheritDoc}
   * 
   * @throws IllegalArgumentException if any of the parameters equals {@code null}.
   */

  @Override
  public final boolean isSupported(final Enum<?> operationId, final Data... operands) {
    checkNotNull(operationId);
    checkNotNull(operands);

    if (0 == operands.length) {
      return false;
    }

    if (operationId == StandardOperation.EQ ||
        operationId == StandardOperation.NOTEQ) {
      return true;
    }

    final DataTypeId typeId = operands[0].getType().getTypeId();
    if (!operations.containsKey(typeId)) {
      return false;
    }

    final Map<OperationId, Operation<OperationId>> operationsForType = operations.get(typeId);
    if (!operationsForType.containsKey(operationId)) {
      return false;
    }

    final Operation<OperationId> operation = operationsForType.get(operationId);
    if (!operation.getOperationArity().isWithinRange(operands.length)) {
      return false;
    }
    return operation.validTypes(operands);
  }

  /**
   * {@inheritDoc}
   * 
   * @throws IllegalArgumentException if any of the parameters equals {@code null}.
   * @throws UnsupportedOperationException if the specified operation is not supported for the
   *         provided operands.
   */

  @Override
  public final Data calculate(final Enum<?> operationId, final Data... operands) {
    checkNotNull(operationId);
    checkNotNull(operands);

    if (!isSupported(operationId, operands)) {
      throw new UnsupportedOperationException(String.format(
        MSG_UNSUPPORTED_FRMT, operationId, operands[0].getType().getTypeId(), operands.length));
    }

    final DataTypeId typeId = operands[0].getType().getTypeId();
    final Map<OperationId, Operation<OperationId>> operationsForType = operations.get(typeId);
    if (operationsForType == null) {
      return evalEquality(operationId, operands);
    }

    final Operation<OperationId> operation = operationsForType.get(operationId);
    if (operation == null) {
      return evalEquality(operationId, operands);
    }

    return operation.calculate(operands);
  }

  private static Data evalEquality(final Enum<?> operationId, final Data ... operands) {
    if (operationId == StandardOperation.EQ) {
      return Data.newBoolean(equalData(operands));
    } else if (operationId == StandardOperation.NOTEQ) {
      return Data.newBoolean(!equalData(operands));
    }
    throw new IllegalArgumentException();
  }

  private static boolean equalData(final Data ... operands) {
    final Data data = operands[0];
    for (int i = 1; i < operands.length; ++i) {
      if (!data.equals(operands[i])) {
        return false;
      }
    }
    return true;
  }

  /**
   * Checks whether all data objects in the specified array have equal types. This is an invariant:
   * operations require data objects that have equal types.
   * 
   * @param operands Array of data objects.
   * @return <code>true</code> if all objects have equal types or <code>false</code> otherwise.
   * 
   * @throws IllegalArgumentException is the parameter equals {@code null}.
   */

  static boolean equalTypes(final Data[] operands) {
    checkNotNull(operands);

    if (operands.length <= 1) {
      return true;
    }

    final DataType type = operands[0].getType();
    for (int index = 1; index < operands.length; ++index) {
      if (!operands[index].getType().equals(type)) {
        return false;
      }
    }

    return true;
  }

  private final String MSG_UNSUPPORTED_FRMT =
    "Failed to calculate: the %s is not supported for the %s type, " +
     "operand types are mismatched or it does not accept %d operands.";

  public static <T extends Enum<T>> Map<T, Operation<T>> operationMap(
      final Class<T> c,
      final Collection<? extends Operation<T>> operations) {
    final Map<T, Operation<T>> map = new EnumMap<>(c);
    for (final Operation<T> op : operations) {
      map.put(op.getOperationId(), op);
    }
    return map;
  }
}
