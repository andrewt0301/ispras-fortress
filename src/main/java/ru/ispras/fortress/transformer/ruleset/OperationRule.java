/*
 * Copyright 2014-2018 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.transformer.ruleset;

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.expression.ExprUtils;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.transformer.TransformerRule;
import ru.ispras.fortress.util.InvariantChecks;

import java.util.Collections;
import java.util.List;
import java.util.Map;

/**
 * OperationRule is a base class for rules applicable to single operation type.
 */
abstract class OperationRule extends DependentRule {
  private final Enum<?> opId;

  /**
   * Create new rule for given operation and register in given ruleset.
   *
   * @param opId Operation identifier for this rule.
   * @param rules Ruleset to register the rule in.
   */
  public OperationRule(final Enum<?> opId, final Map<Enum<?>, TransformerRule> rules) {
    super(rules);
    InvariantChecks.checkNotNull(opId);

    if (rules.containsKey(opId)) {
      throw new IllegalArgumentException("Attempt to override " + opId + " rule");
    }
    // side-effects... saves quite a bit of typing though and provides
    // minor correctness guarantees
    rules.put(opId, this);

    this.opId = opId;
  }

  /**
   * Get operation identifier for this rule.
   */

  public Enum<?> getOperationId() {
    return opId;
  }

  @Override
  public boolean isApplicable(final Node node) {
    return ExprUtils.isOperation(node, opId) && isApplicable((NodeOperation) node);
  }

  /**
   * Helper method to allow additional constraints in derived classes.
   *
   * @return true if derived class accepts given operation node.
   */
  public boolean isApplicable(final NodeOperation op) {
    return true;
  }

  @Override
  public final Node apply(final Node node) {
    return apply((NodeOperation) node);
  }

  public abstract Node apply(NodeOperation node);

  /**
   * Helper method to extract operands from node.
   *
   * @param node Operation node to extract operands from.
   */
  public static Node[] extractOperands(final Node node) {
    final NodeOperation in = (NodeOperation) node;
    final Node[] operands = new Node[in.getOperandCount()];

    for (int i = 0; i < operands.length; ++i) {
      operands[i] = in.getOperand(i);
    }

    return operands;
  }

  /**
   * Check if node represents boolean value.
   *
   * @param node Node instance to be checked.
   *
   * @return true if node is NodeValue instance with boolean type.
   */
  public static boolean isBoolean(final Node node) {
    return node.getKind() == Node.Kind.VALUE
        && node.getDataType() == DataType.BOOLEAN;
  }

  /**
   * Get boolean value of node in unsafe manner.
   *
   * @param node NodeValue instance with boolean type.
   *
   * @return boolean value of given node.
   */

  public static boolean getBoolean(final Node node) {
    return (Boolean) ((NodeValue) node).getValue();
  }

  /**
   * Find first boolean value among operands.
   *
   * @param op Operation which operands are to be looked.
   * @param start Start looking at operands starting with this index.
   *
   * @return Operand index of boolean value, -1 if none found.
   */
  public static int booleanOperandIndex(final NodeOperation op, int start) {
    for (int i = start; i < op.getOperandCount(); ++i) {
      if (isBoolean(op.getOperand(i))) {
        return i;
      }
    }
    return -1;
  }

  static boolean isDistinct(final Node node) {
    return getDistinct(node) != null;
  }

  static NodeOperation getDistinct(final Node node) {
    if (ExprUtils.isOperation(node, StandardOperation.NOTEQ)) {
      return (NodeOperation) node;
    }
    final List<Node> operands = getNotEqOperands(node);
    if (operands.size() == 2) {
      return new NodeOperation(StandardOperation.NOTEQ, operands);
    }
    return null;
  }

  private static List<Node> getNotEqOperands(final Node node) {
    if (ExprUtils.isOperation(node, StandardOperation.NOT)) {
      final Node child = ((NodeOperation) node).getOperand(0);
      if (ExprUtils.isOperation(child, StandardOperation.EQ)) {
        return ((NodeOperation) child).getOperands();
      }
    }
    return Collections.emptyList();
  }
}
