/*
 * Copyright 2016-2018 ISP RAS (http://www.ispras.ru), UniTESK Lab (http://www.unitesk.com)
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package ru.ispras.fortress.transformer;

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.DataTypeId;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.StandardOperation;

import java.math.BigInteger;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

/**
 * Container for transformation rules are applicable for constants casting.
 * @author <a href="mailto:smolov@ispras.ru">Sergey Smolov</a>
 */
final class ConstCastRuleSet {

  static class OperandTypeMap {

    private DataType typeToCast;
    private Map<DataType, Collection<Node>> typeOperandMap;

    public DataType getTypeToCast() {
      return this.typeToCast;
    }

    public void setTypeToCast(final DataType type) {
      this.typeToCast = type;
    }

    public Map<DataType, Collection<Node>> getMap() {
      return this.typeOperandMap;
    }

    public void setMap(final Map<DataType, Collection<Node>> map) {
      this.typeOperandMap = map;
    }
  }

  abstract static class CastConstRule implements TransformerRule {

    protected Map<Node, Node> oldNewMap;
    protected Enum<?> operationId;

    public abstract boolean isApplicable(final NodeOperation operation);

    @Override
    public boolean isApplicable(final Node node) {

      if (!(node instanceof NodeOperation)) {
        return false;
      }

      this.operationId = ((NodeOperation)node).getOperationId();

      return isApplicable((NodeOperation)node) && !this.oldNewMap.isEmpty();
    }

    @Override
    public Node apply(final Node node) {

      final List<Node> casted = new LinkedList<>();
      for (final Node operand : ((NodeOperation) node).getOperands()) {
        casted.add(this.oldNewMap.containsKey(operand) ? this.oldNewMap.get(operand) : operand);
      }
      return new NodeOperation(((NodeOperation)node).getOperationId(), casted);
    }
  }

  private static Collection<Enum<?>> SAME_TYPE = StandardOperation.getSameOperandOperations();
  private static Collection<Enum<?>> INT = StandardOperation.getIntOperandOperations();
  private static Collection<Enum<?>> SAME_BV = StandardOperation.getSameBvOperandOperations();
  private static Collection<Enum<?>> SAME_BOOL = StandardOperation.getBoolOperandOperations();

  // todo: implement constant casting for this case
  private static Collection<Enum<?>> BV_TYPES = StandardOperation.getDifferentBvOperandOperations();

  private static Collection<Enum<?>> LOGIC = StandardOperation.getLogicOperandOperations();
  private static Collection<Enum<?>> SAME_LOGIC_NUM =
      StandardOperation.getSameLogicNumOperandOperations();
  private static Collection<Enum<?>> ONE_INT_PARAM_BV =
      StandardOperation.getOneIntParamBvOperandOperations();
  private static Collection<Enum<?>> TWO_INT_PARAM_BV =
      StandardOperation.getTwoIntParamBvOperandOperations();

  /**
   * Returns constant casting transformer for the specified casting type.
   * @param constCastType Constant casting type.
   * @return Transformer that performs constant operands casting.
   */
  public static NodeTransformer getRuleSet(final Enum<?> constCastType) {

    final NodeTransformer transformer = new NodeTransformer();

    final TransformerRule sameTypeOperands = new CastConstRule() {

      @Override
      public boolean isApplicable(final NodeOperation node) {

        this.oldNewMap = castWrongSameOperands(node, constCastType);
        return SAME_TYPE.contains(this.operationId) || SAME_LOGIC_NUM.contains(this.operationId);
      }
    };

    final TransformerRule intOperands = new CastConstRule() {

      @Override
      public boolean isApplicable(final NodeOperation node) {

        this.oldNewMap = castWrongOperands(node, DataType.INTEGER, constCastType);
        return INT.contains(this.operationId);
      }
    };

    final TransformerRule logicOperands = new CastConstRule() {

      @Override
      public boolean isApplicable(final NodeOperation node) {

        /* Cast non-logic constants to integer for clearness. */
        this.oldNewMap = castWrongOperands(node, DataType.INTEGER, constCastType);
        return LOGIC.contains(this.operationId);
      }
    };

    final TransformerRule sameBvOperands = new CastConstRule() {

      @Override
      public boolean isApplicable(final NodeOperation node) {

        this.oldNewMap = castWrongOperands(node, DataTypeId.BIT_VECTOR, constCastType);
        return SAME_BV.contains(this.operationId);
      }
    };

    final TransformerRule boolOperands = new CastConstRule() {

      @Override
      public boolean isApplicable(final NodeOperation node) {

        this.oldNewMap = castWrongOperands(node, DataType.BOOLEAN, constCastType);
        return SAME_BOOL.contains(this.operationId);
      }
    };

    final TransformerRule oneIntParamBvOperands = new CastConstRule() {
      @Override
      public boolean isApplicable(final NodeOperation node) {

        this.oldNewMap = castWrongParamBvOperands(node, 1, constCastType);
        return ONE_INT_PARAM_BV.contains(this.operationId);
      }
    };

    final TransformerRule twoIntParamBvOperands = new CastConstRule() {
      @Override
      public boolean isApplicable(final NodeOperation node) {

        this.oldNewMap = castWrongParamBvOperands(node, 2, constCastType);
        return TWO_INT_PARAM_BV.contains(this.operationId);
      }
    };

    final TransformerRule selectRule = new CastConstRule() {
      @Override
      public boolean isApplicable(final NodeOperation operation) {

        this.oldNewMap = castWrongArrayOperands(operation, constCastType);
        return StandardOperation.SELECT == this.operationId;
      }
    };

    final TransformerRule storeRule = new CastConstRule() {
      @Override
      public boolean isApplicable(final NodeOperation operation) {

        this.oldNewMap = castWrongArrayOperands(operation, constCastType);
        return StandardOperation.STORE == this.operationId;
      }
    };

    final TransformerRule bvOperands = new CastConstRule() {

      @Override
      public boolean isApplicable(NodeOperation operation) {

        this.oldNewMap = castWrongBvOperands(operation, constCastType);
        return BV_TYPES.contains(this.operationId);
      }
    };

    final TransformerRule iteRule = new CastConstRule() {

      @Override
      public boolean isApplicable(final NodeOperation node) {

        this.oldNewMap = getIfThenElseWrongCond(node);

        return ((NodeOperation) node).getOperationId() == StandardOperation.ITE;
      }

      private Map<Node, Node> getIfThenElseWrongCond(final NodeOperation node) {
        final Map<Node, Node> map = new LinkedHashMap<>();

        DataType varAltType = null;
        DataType constAltType = null;
        final Map<DataType, List<Node>> typeMap = new LinkedHashMap<>();

        for (int i = 0; i < node.getOperandCount(); i++) {

          final Node operand = node.getOperand(i);
          final DataType opType = operand.getDataType();

          if (i == 0 && !opType.equals(DataType.BOOLEAN) && operand instanceof NodeValue) {
            map.put(operand, TypeConversion.coerce(operand, DataType.BOOLEAN, constCastType));
          } else if (i != 0) {

            if (typeMap.containsKey(opType)) {
              typeMap.get(opType).add(operand);
            } else {
              final List<Node> typeNodes = new LinkedList<>();
              typeNodes.add(operand);
              typeMap.put(opType, typeNodes);
            }

            if (!(operand instanceof NodeValue)) {
              varAltType = opType;
            } else {
              constAltType = opType;
            }
          }
        }

        if (defined(varAltType) && constAltType != null && !varAltType.equals(constAltType)) {

          final Node oldOperand = typeMap.get(constAltType).get(0);

          map.put(oldOperand, TypeConversion.coerce(oldOperand, varAltType, constCastType));
        }
        return map;
      }
    };

    /* Register all rules. */

    addRules(transformer, SAME_TYPE, sameTypeOperands);
    addRules(transformer, SAME_LOGIC_NUM, sameTypeOperands);
    addRules(transformer, LOGIC, logicOperands);
    addRules(transformer, INT, intOperands);
    addRules(transformer, SAME_BV, sameBvOperands);
    addRules(transformer, SAME_BOOL, boolOperands);
    addRules(transformer, ONE_INT_PARAM_BV, oneIntParamBvOperands);
    addRules(transformer, TWO_INT_PARAM_BV, twoIntParamBvOperands);
    addRules(transformer, BV_TYPES, bvOperands);

    transformer.addRule(StandardOperation.ITE, iteRule);
    transformer.addRule(StandardOperation.SELECT, selectRule);
    transformer.addRule(StandardOperation.STORE, storeRule);

    return transformer;
  }

  private static boolean defined(final DataType type) {

    return type != null && !type.equals(DataType.UNKNOWN);
  }

  private static Map<Node, Node> castWrongBvOperands(
      final NodeOperation operation,
      final Enum<?> constCastType) {

    final Map<Node, Node> wrongOpMap = new LinkedHashMap<>();

    for (final Node operand : operation.getOperands()) {
      if (operand instanceof NodeValue && !operand.isType(DataTypeId.BIT_VECTOR)) {
        final int size = getBvSize((NodeValue) operand, constCastType);
        final Node castToBv =
            TypeConversion.coerce(operand, DataType.bitVector(size), constCastType);
        wrongOpMap.put(operand, castToBv);
      }
    }

    return wrongOpMap;
  }

  private static int getBvSize(final NodeValue value, final Enum<?> constCastType) {

    switch (value.getDataTypeId()) {
      case BIT_VECTOR:
      case LOGIC_STRING:
        return value.getDataType().getSize();
      case LOGIC_BOOLEAN:
        return 1;
      case LOGIC_INTEGER:
        BigInteger bigInt = value.getInteger();
        return constCastType == TypeConversion.ConstCast.SIGNED
            ? bigInt.bitLength()
            : bigInt.bitCount();
      default:
        return 0;
    }
  }

  private static Map<Node, Node> castWrongArrayOperands(
      final NodeOperation operation,
      final Enum<?> constCastType) {

    final Node array = operation.getOperand(0);

    final DataType arrayType = array.getDataType();
    final DataType keyType = (DataType) arrayType.getAttribute(DataTypeId.Attribute.KEY);

    final Node index = operation.getOperand(1);

    if (index.getKind() != Node.Kind.VALUE || keyType.equals(index.getDataType()))

      return new LinkedHashMap<>();

    else {

      return Collections.singletonMap(index, TypeConversion.coerce(index, keyType, constCastType));
    }
  }

  private static void addRules(
      final NodeTransformer transformer,
      final Collection<Enum<?>> operationIds,
      final TransformerRule sameTypeOperands) {
    for (final Enum<?> opId : operationIds) {
      transformer.addRule(opId, sameTypeOperands);
    }
  }

  private static Map<Node, Node> castWrongSameOperands(
      final NodeOperation node,
      final Enum<?> constCastType) {

    final Map<Node, Node> wrongOpMap = new LinkedHashMap<>();

    final OperandTypeMap opTypeMap = createOperandTypeMap(node);

    if (!allOperandsOfSameType(opTypeMap)) {

      final Map<DataType, Collection<Node>> typeMap = opTypeMap.getMap();
      for (final Map.Entry<DataType, Collection<Node>> typeNodes : typeMap.entrySet()) {

        final DataType typeToCast = opTypeMap.getTypeToCast();
        if (!typeNodes.getKey().equals(typeToCast) && defined(typeToCast)) {
          for (final Node typeNode : typeNodes.getValue()) {
            if (typeNode instanceof NodeValue) {

              final Node casted = TypeConversion.coerce(typeNode, typeToCast, constCastType);
              wrongOpMap.put(typeNode, casted);
            }
          }
        }
      }
    }
    return wrongOpMap;
  }

  private static Map<Node, Node> castWrongOperands(
      final NodeOperation node,
      final DataTypeId typeId,
      final Enum<?> constCastType) {

    final Map<Node, Node> wrongOpMap = new LinkedHashMap<>();

    final OperandTypeMap opTypeMap = createOperandTypeMap(node);
    if (!allOperandsOfSameType(opTypeMap)) {

      final DataType varType = opTypeMap.getTypeToCast();
      final Map<DataType, Collection<Node>> typeMap = opTypeMap.getMap();

      for (final Map.Entry<DataType, Collection<Node>> typeNodes : typeMap.entrySet()) {

        final DataType nodeType = typeNodes.getKey();

        if (typeNodes.getKey() != varType || nodeType.getTypeId() != typeId) {
          for (final Node typeNode : typeNodes.getValue()) {

            if (typeNode instanceof NodeValue && defined(varType)) {
              wrongOpMap.put(typeNode, TypeConversion.coerce(typeNode, varType, constCastType));
            }
          }
        }
      }
    }

    return wrongOpMap;
  }

  private static Map<Node, Node> castWrongOperands(
      final NodeOperation node,
      final DataType dataType,
      final Enum<?> constCastType) {

    final Map<Node, Node> wrongOpMap = new LinkedHashMap<>();

    for (final Node operand : node.getOperands()) {
      if (operand instanceof NodeValue
          && !operand.getDataType().equals(dataType)
          && defined(dataType)) {
        wrongOpMap.put(operand, TypeConversion.coerce(operand, dataType, constCastType));
      }
    }

    return wrongOpMap;
  }

  private static OperandTypeMap createOperandTypeMap(final NodeOperation operation) {
    final OperandTypeMap operandTypeMap = new OperandTypeMap();

    DataType typeToCast = null;
    boolean typeOfNonValue = false;
    final Map<DataType, Collection<Node>> typeMap = new LinkedHashMap<>();

    for (final Node operand : operation.getOperands()) {
      final DataType dataType = operand.getDataType();

      /* Set as 'type-to-be-casted-to' the type of non-constant operand
       * or the biggest in size type of constant operand. */
      if ((!(operand instanceof NodeValue))
          || (!typeOfNonValue
              && (typeToCast == null || typeToCast.getSize() < dataType.getSize()))) {
        typeToCast = dataType;
        if (!(operand instanceof NodeValue)) {
          typeOfNonValue = true;
        }
      }

      if (typeMap.containsKey(dataType)) {
        typeMap.get(dataType).add(operand);
      } else {
        final Collection<Node> nodes = new LinkedList<>();
        nodes.add(operand);
        typeMap.put(dataType, nodes);
      }
    }
    operandTypeMap.setTypeToCast(typeToCast);
    operandTypeMap.setMap(typeMap);

    return operandTypeMap;
  }

  private static boolean allOperandsOfSameType(OperandTypeMap operandTypeMap) {

    return operandTypeMap.getMap().size() == 1;
  }

  private static Map<Node, Node> castWrongParamBvOperands(
      final NodeOperation node,
      final int paramNum,
      final Enum<?> constCastType) {

    final Map<Node, Node> map = new LinkedHashMap<>();

    for (int i = 0; i < node.getOperandCount(); i++) {

      final Node operand = node.getOperand(i);
      if (operand instanceof NodeValue
          && i < paramNum
          && !operand.getDataType().equals(DataType.INTEGER)) {
        map.put(operand, TypeConversion.coerce(operand, DataType.INTEGER, constCastType));
      }
    }

    return map;
  }
}
