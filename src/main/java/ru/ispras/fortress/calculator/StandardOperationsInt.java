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

import java.math.BigInteger;
import java.util.Collections;
import java.util.EnumMap;
import java.util.Map;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataTypeId;
import ru.ispras.fortress.expression.StandardOperation;

/**
 * The StandardOperationsInt enumeration holds a collection of operation objects that are
 * responsible for performing standard operations (StandardOperation) on data objects that hold
 * integers (DataTypeId.LOGIC_INTEGER).
 * 
 * <p>
 * Implementation details and conventions common for all operation groups implemented as
 * enumerations:
 * 
 * <ol>
 * <li>The enumeration implements the Operation interface parameterized with the StandardOperation
 * type.
 * 
 * <li>Each operation is represented by an element of the enumeration that provides implementation
 * for the "calculate" methods with one and two parameters. If one of the overloaded "calculate"
 * method is not applicable for the operation the UnsupportedOperationException runtime exception is
 * thrown.
 * 
 * <li>Each enumeration elements holds operation identifier and the range of the allowed operand
 * number.
 * 
 * <li>The enumeration provides the "dataTypeId" static method that returns the identifier of the
 * data type for which the enumeration provides operations.
 * </ol>
 * 
 * @author Andrei Tatarnikov
 */

enum StandardOperationsInt implements Operation<StandardOperation> {

  PLUS(StandardOperation.PLUS, ArityRange.UNARY) {
    @Override
    public Data calculate(Data... operands) {
      return operands[0];
    }
  },

  MINUS(StandardOperation.MINUS, ArityRange.UNARY) {
    @Override
    public Data calculate(Data... operands) {
      return Data.newInteger(toBigInteger(operands[0]).negate());
    }
  },

  ADD(StandardOperation.ADD, ArityRange.BINARY_UNBOUNDED) {
    @Override
    public Data calculate(Data... operands) {
      BigInteger result = toBigInteger(operands[0]);
      for (int index = 1; index < operands.length; ++index) {
        result = result.add(toBigInteger(operands[index]));
      }

      return Data.newInteger(result);
    }
  },

  SUB(StandardOperation.SUB, ArityRange.BINARY_UNBOUNDED) {
    @Override
    public Data calculate(Data... operands) {
      BigInteger result = toBigInteger(operands[0]);
      for (int index = 1; index < operands.length; ++index) {
        result = result.subtract(toBigInteger(operands[index]));
      }

      return Data.newInteger(result);
    }
  },

  MUL(StandardOperation.MUL, ArityRange.BINARY_UNBOUNDED) {
    @Override
    public Data calculate(Data... operands) {
      BigInteger result = toBigInteger(operands[0]);
      for (int index = 1; index < operands.length; ++index) {
        result = result.multiply(toBigInteger(operands[index]));
      }

      return Data.newInteger(result);
    }
  },

  DIV(StandardOperation.DIV, ArityRange.BINARY) {
    @Override
    public Data calculate(Data... operands) {
      final BigInteger value1 = toBigInteger(operands[0]);
      final BigInteger value2 = toBigInteger(operands[1]);

      return Data.newInteger(value1.divide(value2));
    }
  },

  REM(StandardOperation.REM, ArityRange.BINARY) {
    @Override
    public Data calculate(Data... operands) {
      // Implemented like in Z3: the result is negative only
      // if the second operand is negative.

      final BigInteger value1 = toBigInteger(operands[0]);
      final BigInteger value2 = toBigInteger(operands[1]);

      final BigInteger result = value1.divideAndRemainder(value2)[1].abs();
      return Data.newInteger(value2.compareTo(BigInteger.ZERO) < 0 ? result.negate() : result);
    }
  },

  MOD(StandardOperation.MOD, ArityRange.BINARY) {
    @Override
    public Data calculate(Data... operands) {
      // Implemented like in Z3: The result is always non-negative.

      final BigInteger value1 = toBigInteger(operands[0]);
      final BigInteger value2 = toBigInteger(operands[1]);

      return Data.newInteger(value1.mod(value2.abs()));
    }
  };

  private static final Map<StandardOperation, Operation<StandardOperation>> operations;

  static {
    final Map<StandardOperation, Operation<StandardOperation>> map =
      new EnumMap<StandardOperation, Operation<StandardOperation>>(StandardOperation.class);

    for (Operation<StandardOperation> value : values())
      map.put(value.getOperationId(), value);

    operations = Collections.unmodifiableMap(map);
  }

  public static Map<StandardOperation, Operation<StandardOperation>> operations() {
    return operations;
  }

  private final StandardOperation operationId;
  private final ArityRange operationArity;

  private StandardOperationsInt(StandardOperation operationId, ArityRange operationArity) {
    this.operationId = operationId;
    this.operationArity = operationArity;
  }

  public static DataTypeId dataTypeId() {
    return DataTypeId.LOGIC_INTEGER;
  }

  @Override
  public final StandardOperation getOperationId() {
    return operationId;
  }

  @Override
  public final ArityRange getOperationArity() {
    return operationArity;
  }

  private static BigInteger toBigInteger(Data data) {
    assert data.getType().getValueClass().equals(BigInteger.class);
    return (BigInteger) data.getValue();
  }
}
