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
import ru.ispras.fortress.data.types.datamap.DataMap;
import ru.ispras.fortress.expression.ExprUtils;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.Nodes;
import ru.ispras.fortress.util.InvariantChecks;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

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
   * @throws IllegalArgumentException when node argument is {@code null}.
   *
   * @return Node every constant sub-..node of that is casted to be a correct operand of
   *         related operation.
   */
  public static Node castConstants(final Node node, final Enum<?> constCastKind) {
    InvariantChecks.checkNotNull(node);

    final NodeTransformer transformer = ConstCastRuleSet.getRuleSet(constCastKind);
    transformer.walk(Reducer.reduce(node).deepCopy());

    final List<Node> result = transformer.getResult();
    return result.size() == 1
        ? result.iterator().next()
        : ExprUtils.getConjunction(result.toArray(new Node[result.size()]));
  }

  /**
   * Casts constant sub-...operands of the specified node supposing that casting is unsigned.
   * @param node Node to be processed.
   * @return A new node, every constant sub-...operand of that is casted to be a correct operand
   *         of related operation.
   */
  public static Node castConstants(final Node node) {
    return castConstants(Reducer.reduce(node), ConstCast.UNSIGNED);
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

    /* The map conversion. */
    /* NOTE: this implementation works properly when the sum of map value sizes
             is equal to resulting bit vector size. */
    if (srcType.getTypeId().equals(DataTypeId.MAP)) {
      if (!node.getKind().equals(Node.Kind.VALUE)) {
        return null;
      }

      DataType keyType = (DataType)srcType.getAttribute(DataTypeId.Attribute.KEY);

      switch (type.getTypeId()) {
        case BIT_VECTOR:
          final DataMap array = ((NodeValue) node).getArray();
          final String bitString = map2BitString(array, keyType, sizeOf(type));

          return NodeValue.newBitVector(BitVector.valueOf(bitString));
        default:
          return null;
      }
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
          return Nodes.bvzeroext(sizeOf(type) - sizeOf(srcType), node);
        } else {
          return Nodes.bvextract(type.getSize(), 0, node);
        }
    }
    return null;
  }

  private static String map2BitString(
      final DataMap map,
      final DataType keyType,
      final int size) {

    final Comparator<Data> dataComparator = new Comparator<Data>() {

      @Override
      public int compare(final Data obj, final Data arg) {

        final DataTypeId keyTypeId = keyType.getTypeId();

        switch (keyTypeId) {
          case BIT_VECTOR:
            final BitVector objVector = obj.getBitVector();
            final BitVector argVector = arg.getBitVector();
            return objVector.compareTo(argVector);
          case LOGIC_BOOLEAN:
            final boolean objBool = obj.getBoolean();
            final boolean argBool = arg.getBoolean();
            if (objBool ^ argBool) {
              if (objBool) {
                return 1;
              } else {
                return -1;
              }
            } else {
              return 0;
            }
          case LOGIC_INTEGER:
            final BigInteger objInt = obj.getInteger();
            final BigInteger argInt = arg.getInteger();
            return objInt.compareTo(argInt);
          default:
            throw new UnsupportedOperationException(
                "Unable to convert map with key type id: " + keyTypeId);
        }
      }
    };

    final Set<Data> keys = new TreeSet<>(dataComparator);
    keys.addAll(map.keySet());
    final List<String> values = new LinkedList<>();
    for (final Data key : keys) {
      final Data value = map.get(key);
      values.add(value.getValue().toString());
    }
    /* Convert to little-endian. */
    Collections.reverse(values);

    int mapLength = 0;

    final StringBuilder builder = new StringBuilder();
    for (final String mapValue : values) {
      mapLength += mapValue.length();
      builder.append(mapValue);
    }
    if (mapLength != size) {
      throw new IllegalStateException(
          String.format(
              "%s bit size vector cannot be created from %s bit size string.",
              size,
              mapLength));
    }

    return builder.toString();
  }

  public static NodeValue valueOf(final BigInteger value, final DataType type) {
    checkNotNull(value);
    checkNotNull(type);
    checkTrue(isIntegral(type));

    switch (type.getTypeId()) {
    case BIT_VECTOR: return NodeValue.newBitVector(value, type.getSize());
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
    return Nodes.noteq(node, NodeValue.newBitVector(BigInteger.ZERO, node.getDataType().getSize()));
  }

  private static NodeOperation bool2bv(final Node node, final int size) {
    return Nodes.ite(node, NodeValue.newBitVector(BigInteger.ONE, size),
                           NodeValue.newBitVector(BigInteger.ZERO, size));
  }

  private static NodeOperation int2bool(final Node node) {
    return Nodes.noteq(node, NodeValue.newInteger(BigInteger.ZERO));
  }

  private static NodeOperation bool2int(final Node node) {
    return Nodes.ite(node, NodeValue.newInteger(BigInteger.ONE),
                           NodeValue.newInteger(BigInteger.ZERO));
  }
}
