/*
 * Copyright 2014-2015 ISP RAS (http://www.ispras.ru)
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

import java.util.Collections;
import java.util.EnumMap;
import java.util.Map;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.DataTypeId;
import ru.ispras.fortress.data.types.bitvector.BitVector;
import ru.ispras.fortress.expression.StandardOperation;

/**
 * The {@link StandardOperationsBool} enumeration holds a collection of operation objects that are
 * responsible for performing standard operations (StandardOperation) on data objects that hold
 * booleans {@link DataTypeId#LOGIC_BOOLEAN}.
 *
 * <p>Implementation details and conventions common for all operation groups implemented
 * as enumerations:
 *
 * <ol><li>The enumeration implements the Operation interface parameterized with
 * the StandardOperation type.
 * <li>Each operation is represented by an element of the enumeration that provides implementation
 * for the "calculate" methods with one and two parameters. If one of the overloaded "calculate"
 * method is not applicable for the operation the UnsupportedOperationException runtime exception is
 * thrown.
 * <li>Each enumeration elements holds operation identifier and the range of the allowed operand
 * number.
 * <li>The enumeration provides the "dataTypeId" static method that returns the identifier of the
 * data type for which the enumeration provides operations.</ol>
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
enum StandardOperationsBool implements Operation<StandardOperation> {

  NOT(StandardOperation.NOT, ArityRange.UNARY) {
    @Override
    public Data calculate(final Data... operands) {
      return Data.newBoolean(!operands[0].getBoolean());
    }
  },

  AND(StandardOperation.AND, ArityRange.UNARY_UNBOUNDED) {
    @Override
    public Data calculate(final Data... operands) {
      for (int index = 0; index < operands.length; ++index) {
        if (!operands[index].getBoolean()) {
          return Data.newBoolean(false);
        }
      }
      return Data.newBoolean(true);
    }
  },

  OR(StandardOperation.OR, ArityRange.UNARY_UNBOUNDED) {
    @Override
    public Data calculate(final Data... operands) {
      for (int index = 0; index < operands.length; ++index) {
        if (operands[index].getBoolean()) {
          return Data.newBoolean(true);
        }
      }
      return Data.newBoolean(false);
    }
  },

  XOR(StandardOperation.XOR, ArityRange.BINARY_UNBOUNDED) {
    @Override
    public Data calculate(final Data... operands) {
      boolean result = operands[0].getBoolean();
      for (int index = 1; index < operands.length; ++index) {
        result ^= operands[index].getBoolean();
      }
      return Data.newBoolean(result);
    }
  },

  IMPL(StandardOperation.IMPL, ArityRange.BINARY) {
    @Override
    public Data calculate(final Data... operands) {
      final boolean value1 = operands[0].getBoolean();
      final boolean value2 = operands[1].getBoolean();

      return Data.newBoolean(!value1 || value2);
    }
  },

  ITE(StandardOperation.ITE, ArityRange.TERNARY) {
    @Override
    public Data calculate(final Data... operands) {
      if (operands[0].getBoolean()) {
        return operands[1];
      }
      return operands[2];
    }

    @Override
    public boolean validTypes(final Data... operands) {
      return operands[0].getType().equals(DataType.BOOLEAN) &&
             operands[1].getType().equals(operands[2].getType());
    }
  },

  BOOL2BV(StandardOperation.BOOL2BV, ArityRange.UNARY) {
    @Override
    public Data calculate(final Data... operands) {
      if (operands[0].getBoolean()) {
        return Data.newBitVector(BitVector.TRUE);
      }
      return Data.newBitVector(BitVector.FALSE);
    }
  };

  private static final Map<StandardOperation, Operation<StandardOperation>> OPERATIONS;
  static {
    final Map<StandardOperation, Operation<StandardOperation>> map =
        new EnumMap<>(StandardOperation.class);

    for (final Operation<StandardOperation> value : values()) {
      map.put(value.getOperationId(), value);
    }

    OPERATIONS = Collections.unmodifiableMap(map);
  }

  public static Map<StandardOperation, Operation<StandardOperation>> operations() {
    return OPERATIONS;
  }

  private final StandardOperation operationId;
  private final ArityRange operationArity;

  private StandardOperationsBool(
      final StandardOperation operationId,
      final ArityRange operationArity) {
    this.operationId = operationId;
    this.operationArity = operationArity;
  }

  public static DataTypeId dataTypeId() {
    return DataTypeId.LOGIC_BOOLEAN;
  }

  @Override
  public final StandardOperation getOperationId() {
    return operationId;
  }

  @Override
  public final ArityRange getOperationArity() {
    return operationArity;
  }

  @Override
  public boolean validTypes(final Data... operands) {
    return Data.equalTypes(operands);
  }
}
