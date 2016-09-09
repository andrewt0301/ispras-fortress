/*
 * Copyright 2016 ISP RAS (http://www.ispras.ru), UniTESK Lab (http://www.unitesk.com)
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

import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

/**
 * @author <a href="mailto:smolov@ispras.ru">Sergey Smolov</a>
 */
final class ConstCastRuleSet {

  /**
   * Constant operands casting types.
   */
  public enum ConstCast {

    /**
     * No casting for constant operands is required.
     */
    NONE,

    /**
     * Signed casting for constant operands is required.
     */
    SIGNED_CAST,

    /**
     * Unsigned casting for constant operands is required.
     */
    UNSIGNED_CAST,
  }

  static class OperandTypeMap {

    private DataType varType;
    private Map<DataType, Collection<Node>> typeOperandMap;

    public DataType getVarType() {
      return this.varType;
    }

    public void setVarType(final DataType type) {
      this.varType = type;
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
  private static Collection<Enum<?>> BV_TYPES = StandardOperation.getBvOperandOperations();

  private static Collection<Enum<?>> LOGIC = StandardOperation.getLogicOperandOperations();
  private static Collection<Enum<?>> SAME_LOGIC_NUM =
      StandardOperation.getSameLogicNumOperandOperations();
  private static Collection<Enum<?>> ONE_INT_PARAM_BV =
      StandardOperation.getOneIntParamBvOperandOperations();
  private static Collection<Enum<?>> TWO_INT_PARAM_BV =
      StandardOperation.getTwoIntParamBvOperandOperations();

  // TODO: take const casting type into account

  public static NodeTransformer getRuleSet(final Enum<?> constCastType) {

    final NodeTransformer transformer = new NodeTransformer();

    final TransformerRule sameTypeOperands = new CastConstRule() {

      @Override
      public boolean isApplicable(final NodeOperation node) {

        this.oldNewMap = castWrongSameOperands(node);
        return SAME_TYPE.contains(this.operationId) || SAME_LOGIC_NUM.contains(this.operationId);
      }
    };

    final TransformerRule intOperands = new CastConstRule() {

      @Override
      public boolean isApplicable(final NodeOperation node) {

        this.oldNewMap = castWrongOperands(node, DataType.INTEGER);
        return INT.contains(this.operationId);
      }
    };

    final TransformerRule logicOperands = new CastConstRule() {

      @Override
      public boolean isApplicable(final NodeOperation node) {

        /* Cast non-logic constants to integer for clearness. */
        this.oldNewMap = castWrongOperands(node, DataType.INTEGER);
        return LOGIC.contains(this.operationId);
      }
    };

    final TransformerRule sameBvOperands = new CastConstRule() {

      @Override
      public boolean isApplicable(final NodeOperation node) {

        this.oldNewMap = castWrongOperands(node, DataTypeId.BIT_VECTOR);
        return SAME_BV.contains(this.operationId);
      }
    };

    final TransformerRule boolOperands = new CastConstRule() {

      @Override
      public boolean isApplicable(final NodeOperation node) {

        this.oldNewMap = castWrongOperands(node, DataType.BOOLEAN);
        return SAME_BOOL.contains(this.operationId);
      }
    };

    final TransformerRule oneIntParamBvOperands = new CastConstRule() {
      @Override
      public boolean isApplicable(final NodeOperation node) {

        this.oldNewMap = castWrongParamBvOperands(node, 1);
        return ONE_INT_PARAM_BV.contains(this.operationId);
      }
    };

    final TransformerRule twoIntParamBvOperands = new CastConstRule() {
      @Override
      public boolean isApplicable(final NodeOperation node) {

        this.oldNewMap = castWrongParamBvOperands(node, 2);
        return TWO_INT_PARAM_BV.contains(this.operationId);
      }
    };

    final TransformerRule selectRule = new CastConstRule() {
      @Override
      public boolean isApplicable(final NodeOperation operation) {

        this.oldNewMap = castWrongArrayOperands(operation);
        return StandardOperation.SELECT == this.operationId;
      }
    };

    final TransformerRule storeRule = new CastConstRule() {
      @Override
      public boolean isApplicable(final NodeOperation operation) {

        this.oldNewMap = castWrongArrayOperands(operation);
        return StandardOperation.STORE == this.operationId;
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

        DataType varType = null;
        DataType constType = null;
        final Map<DataType, List<Node>> typeMap = new LinkedHashMap<>();

        for (int i = 0; i < node.getOperandCount(); i++) {

          final Node operand = node.getOperand(0);
          final DataType opType = operand.getDataType();

          if (i == 0 && !opType.equals(DataType.BOOLEAN) && operand instanceof NodeValue) {
            map.put(operand, TypeConversion.coerce(operand, DataType.BOOLEAN));
          } else {

            if (typeMap.containsKey(opType)) {
              typeMap.get(opType).add(operand);
            } else {
              final List<Node> typeNodes = new LinkedList<>();
              typeNodes.add(operand);
              typeMap.put(opType, typeNodes);
            }

            if (!(operand instanceof NodeValue)) {
              varType = opType;
            } else {
              constType = opType;
            }
          }
        }

        if (varType != null && constType != null && !varType.equals(constType)) {

          final Node oldOperand = typeMap.get(constType).get(0);

          map.put(oldOperand, TypeConversion.coerce(oldOperand, varType));
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

    transformer.addRule(StandardOperation.ITE, iteRule);
    transformer.addRule(StandardOperation.SELECT, selectRule);
    transformer.addRule(StandardOperation.STORE, storeRule);

    return transformer;
  }

  private static Map<Node, Node> castWrongArrayOperands(final NodeOperation operation) {

    final Node index = operation.getOperand(1);
    return index instanceof NodeValue && !index.isType(DataType.INTEGER)
        ? Collections.singletonMap(index, TypeConversion.coerce(index, DataType.INTEGER))
        : new LinkedHashMap<Node, Node>();
  }

  private static void addRules(
      final NodeTransformer transformer,
      final Collection<Enum<?>> operationIds,
      final TransformerRule sameTypeOperands) {
    for (final Enum<?> opId : operationIds) {
      transformer.addRule(opId, sameTypeOperands);
    }
  }

  private static Map<Node, Node> castWrongSameOperands(final NodeOperation node) {

    final Map<Node, Node> wrongOpMap = new LinkedHashMap<>();

    final OperandTypeMap opTypeMap = createOperandTypeMap(node);

    if (!allOperandsOfSameType(opTypeMap)) {

      final Map<DataType, Collection<Node>> typeMap = opTypeMap.getMap();
      for (final Map.Entry<DataType, Collection<Node>> typeNodes : typeMap.entrySet()) {
        if (typeNodes.getKey() != opTypeMap.getVarType()) {
          for (final Node typeNode : typeNodes.getValue()) {
            if (typeNode instanceof NodeValue) {
              wrongOpMap.put(typeNode, TypeConversion.coerce(typeNode, opTypeMap.getVarType()));
            }
          }
        }
      }
    }
    return wrongOpMap;
  }

  private static Map<Node, Node> castWrongOperands(
    final NodeOperation node,
    final DataTypeId typeId) {

    final Map<Node, Node> wrongOpMap = new LinkedHashMap<>();

    final OperandTypeMap opTypeMap = createOperandTypeMap(node);
    if (!allOperandsOfSameType(opTypeMap)) {

      final DataType varType = opTypeMap.getVarType();
      final Map<DataType, Collection<Node>> typeMap = opTypeMap.getMap();

      for (final Map.Entry<DataType, Collection<Node>> typeNodes : typeMap.entrySet()) {

        final DataType nodeType = typeNodes.getKey();

        if (typeNodes.getKey() != varType || nodeType.getTypeId() != typeId) {
          for (final Node typeNode : typeNodes.getValue()) {

            if (typeNode instanceof NodeValue) {
              wrongOpMap.put(typeNode, TypeConversion.coerce(typeNode, varType));
            }
          }
        }
      }
    }

    return wrongOpMap;
  }

  private static OperandTypeMap createOperandTypeMap(final NodeOperation operation) {
    final OperandTypeMap operandTypeMap = new OperandTypeMap();

    DataType varType = null;
    final Map<DataType, Collection<Node>> typeMap = new LinkedHashMap<>();

    for (final Node operand : operation.getOperands()) {
      final DataType dataType = operand.getDataType();
      if (! (operand instanceof NodeValue) && varType == null) {
        varType = dataType;
      }

      if (typeMap.containsKey(dataType)) {
        typeMap.get(dataType).add(operand);
      } else {
        final Collection<Node> nodes = new LinkedList<>();
        nodes.add(operand);
        typeMap.put(dataType, nodes);
      }
    }
    operandTypeMap.setVarType(varType);
    operandTypeMap.setMap(typeMap);

    return operandTypeMap;
  }

  private static Map<Node, Node> castWrongOperands(
      final NodeOperation node,
      final DataType dataType) {

    final Map<Node, Node> wrongOpMap = new LinkedHashMap<>();

    for (final Node operand : node.getOperands()) {
      if (operand instanceof NodeValue && operand.getDataType() != dataType) {
        wrongOpMap.put(operand, TypeConversion.coerce(operand, dataType));
      }
    }

    return wrongOpMap;
  }

  private static boolean allOperandsOfSameType(OperandTypeMap operandTypeMap) {

    return operandTypeMap.getMap().size() == 1;
  }

  private static Map<Node, Node> castWrongParamBvOperands(
      final NodeOperation node,
      final int paramNum) {

    final Map<Node, Node> map = new LinkedHashMap<>();

    for (int i = 0; i < node.getOperandCount(); i++) {

      final Node operand = node.getOperand(i);
      if (operand instanceof NodeValue
          && i < paramNum
          && !operand.getDataType().equals(DataType.INTEGER)) {
        map.put(operand, TypeConversion.coerce(operand, DataType.INTEGER));
      }
    }

    return map;
  }
}
