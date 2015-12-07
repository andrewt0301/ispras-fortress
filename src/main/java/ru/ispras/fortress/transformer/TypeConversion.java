/*
 * Copyright 2015 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.transformer;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.DataTypeId;
import ru.ispras.fortress.data.types.bitvector.BitVector;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.StandardOperation;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.List;

import static ru.ispras.fortress.util.InvariantChecks.checkNotNull;
import static ru.ispras.fortress.util.InvariantChecks.checkTrue;

public final class TypeConversion {
  private static final List<DataTypeId> integralTypes =
      Arrays.asList(DataTypeId.LOGIC_BOOLEAN, DataTypeId.BIT_VECTOR, DataTypeId.LOGIC_INTEGER);

  private TypeConversion() {}

  public static Node coerce(final Node node, final DataType type) {
    checkNotNull(node);
    checkNotNull(type);

    final DataType srcType = node.getDataType();
    if (srcType.equals(type)) {
      return node;
    }
    if (!isIntegral(node) || !isIntegral(type)) {
      return null;
    }

    switch (node.getKind()) {
    case VALUE: return valueOf(integerValue((NodeValue) node, false), type);

    case VARIABLE:
    case OPERATION:
      checkTrue(!bv2natRequired(srcType, type), "Bit-vector expression can not be cast to integer");
      checkTrue(!bv2natRequired(type, srcType), "Integer expression can not be cast to bit-vector");

      if (node.isType(DataTypeId.LOGIC_BOOLEAN)) {
        if (type.getTypeId().equals(DataTypeId.LOGIC_INTEGER)) {
          return bool2int(node);
        } else {
          return bool2bv(node, type.getSize());
        }
      } else if (type.getTypeId().equals(DataTypeId.LOGIC_BOOLEAN)) {
        if (node.isType(DataTypeId.LOGIC_INTEGER)) {
          return int2bool(node);
        } else {
          return bv2bool(node);
        }
      } else if (sizeOf(srcType) < sizeOf(type)) {
        return new NodeOperation(StandardOperation.BVZEROEXT,
                                 NodeValue.newInteger(sizeOf(type) - sizeOf(srcType)),
                                 node);
      } else {
        return new NodeOperation(StandardOperation.BVEXTRACT,
                                 NodeValue.newInteger(type.getSize()),
                                 NodeValue.newInteger(0),
                                 node);
      }
    }
    return null;
  }

  public static NodeValue valueOf(final BigInteger value, final DataType type) {
    checkNotNull(value);
    checkNotNull(type);
    checkTrue(isIntegral(type));

    switch (type.getTypeId()) {
    case BIT_VECTOR: return NodeValue.newBitVector(BitVector.valueOf(value, type.getSize()));
    case LOGIC_BOOLEAN: return NodeValue.newBoolean(!value.equals(BigInteger.ZERO));
    case LOGIC_INTEGER: return NodeValue.newInteger(value);
    }
    throw new IllegalStateException();
  }

  public static BigInteger integerValue(final NodeValue value, final boolean signed) {
    checkNotNull(value);
    checkTrue(isIntegral(value));

    if (value.isType(DataTypeId.BIT_VECTOR)) {
      return value.getBitVector().bigIntegerValue(signed);
    }
    if (value.isType(DataTypeId.LOGIC_BOOLEAN)) {
      return (value.getBoolean()) ? BigInteger.ONE : BigInteger.ZERO;
    }
    return value.getInteger();
  }

  public static boolean isIntegral(final Node node) {
    checkNotNull(node);
    return isIntegral(node.getDataType());
  }

  public static boolean isIntegral(final DataType type) {
    checkNotNull(type);
    return integralTypes.contains(type.getTypeId());
  }

  private static int sizeOf(final DataType type) {
    switch (type.getTypeId()) {
    case BIT_VECTOR: return type.getSize();
    case LOGIC_BOOLEAN: return 1;
    case LOGIC_INTEGER: return Integer.MAX_VALUE;
    }
    return -1;
  }

  private static boolean bv2natRequired(final DataType src, final DataType dst) {
    return src.getTypeId().equals(DataTypeId.BIT_VECTOR) &&
           src.getSize() > 1 &&
           dst.getTypeId().equals(DataTypeId.LOGIC_INTEGER);
  }

  private static NodeOperation bv2bool(final Node node) {
    return new NodeOperation(StandardOperation.NOTEQ,
                             node,
                             newBitVector(BigInteger.ZERO, node.getDataType().getSize()));
  }

  private static NodeOperation bool2bv(final Node node, final int size) {
    return new NodeOperation(StandardOperation.ITE,
                             node,
                             newBitVector(BigInteger.ONE, size),
                             newBitVector(BigInteger.ZERO, size));
  }

  private static NodeOperation int2bool(final Node node) {
    return new NodeOperation(StandardOperation.NOTEQ,
                             node,
                             NodeValue.newInteger(BigInteger.ZERO));
  }

  private static NodeOperation bool2int(final Node node) {
    return new NodeOperation(StandardOperation.ITE,
                             node,
                             NodeValue.newInteger(BigInteger.ONE),
                             NodeValue.newInteger(BigInteger.ZERO));
  }

  private static NodeValue newBitVector(final BigInteger value, final int size) {
    return NodeValue.newBitVector(BitVector.valueOf(value, size));
  }
}
