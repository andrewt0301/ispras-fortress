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

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.DataTypeId;
import ru.ispras.fortress.data.types.bitvector.BitVector;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.StandardOperation;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import static ru.ispras.fortress.util.InvariantChecks.checkNotNull;
import static ru.ispras.fortress.util.InvariantChecks.checkTrue;

public final class TypeConversion {

  /**
   * Constant operands casting types.
   */
  public enum ConstCast {

    /**
     * Signed casting for constant operands is required.
     */
    SIGNED,

    /**
     * Unsigned casting for constant operands is required (a default value).
     */
    UNSIGNED,
  }

  private static final List<DataTypeId> integralTypes =
      Arrays.asList(DataTypeId.LOGIC_BOOLEAN, DataTypeId.BIT_VECTOR, DataTypeId.LOGIC_INTEGER);

  private TypeConversion() { /* Empty. */ }

  /**
   * Casts constant sub-...operands of the specified node through the specified casting type.
   *
   * @param node Node to be processed.
   * @param constCastKind Constant casting type descriptor (signed, unsigned, etc.).
   *
   * @throws IllegalArgumentException when any of the arguments
   *         (except casting type) is {@code null}.
   *
   * @return Nodes every constant sub-..node of that are casted to be correct operands of
   *         corresponding operations.
   */
  public static Collection<Node> castConstants(
      final Node node,
      final Enum<?> constCastKind) {
    checkNotNull(node);

    final NodeTransformer transformer = ConstCastRuleSet.getRuleSet(constCastKind);
    transformer.walk(node.deepCopy());

    return transformer.getResult();
  }

  /**
   * Converts the specified node to the specified data type producing a new node.
   * @param node Node to be converted.
   * @param type Data type of the new node to be produced.
   * @return A new node that has the specified data type but the rest of it's data are taken
   *         from the specified node.
   */
  public static Node coerce(final Node node, final DataType type) {
    return coerce(node, type, ConstCast.UNSIGNED);
  }

  /**
   * Converts the specified node to the specified data type with some constant casting if needed.
   * <p>If the specified node has the same data type as specified, no constant casting
   * is applied.</p>
   * @param node Node to be converted.
   * @param type Data type of the new node to be produced.
   * @param constCastType Constant operands casting mode.
   * @return A new node that has the specified data type but the rest of it's data are taken
   *         from the specified node. Constant sub-...operands are casted in correspondence
   *         with the specified mode.
   * @throws IllegalArgumentException when either node or data type argument is {@code null}.
   */
  public static Node coerce(final Node node, final DataType type, final Enum<?> constCastType) {
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
      case VALUE:
        return valueOf(integerValue((NodeValue) node, constCastType == ConstCast.SIGNED), type);

      case VARIABLE:
      case OPERATION:
        if (bv2natRequired(srcType, type) ||
            bv2natRequired(type, srcType)) {
          return null;
        }

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
