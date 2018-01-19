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

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import ru.ispras.fortress.expression.ExprUtils;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.transformer.TransformerRule;

/**
 * UnrollClause is a helper class implementing standard AND and OR rules.
 */
final class UnrollClause extends OperationRule {
  private final boolean symbol;

  UnrollClause(final StandardOperation op, final Map<Enum<?>, TransformerRule> rules) {
    super(op, rules);
    if (op == StandardOperation.AND) {
      this.symbol = false;
    } else if (op == StandardOperation.OR) {
      this.symbol = true;
    } else {
      throw new IllegalArgumentException();
    }
  }

  @Override
  public boolean isApplicable(final NodeOperation in) {
    for (int i = 0; i < in.getOperandCount(); ++i) {
      final Node operand = in.getOperand(i);
      if (isBoolean(operand)
          || ExprUtils.isOperation(operand, this.getOperationId())
          || appliesTo(operand)) {
        return true;
      }
    }
    return false;
  }

  private boolean appliesTo(final Node node) {
    if (getOperationId().equals(StandardOperation.AND)) {
      return ExprUtils.isOperation(node, StandardOperation.EQ) || isDistinct(node);
    }
    return false;
  }

  @Override
  public Node apply(final NodeOperation op) {
    int numBoolean = 0;
    for (final Node operand : op.getOperands()) {
      if (isBoolean(operand)) {
        if (getBoolean(operand) == this.symbol) {
          return operand;
        } else {
          ++numBoolean;
        }
      }
    }
    if (numBoolean == op.getOperandCount()) {
      return op.getOperand(0);
    }
    final List<Node> operands = this.flattenFilter(op);
    if (!this.postprocess(operands)) {
      return NodeValue.newBoolean(false);
    }
    if (operands.size() == 1) {
      return operands.get(0);
    }
    return new NodeOperation(this.getOperationId(), operands);
  }

  private List<Node> flattenFilter(final NodeOperation op) {
    final List<Node> operands = new ArrayList<>(op.getOperandCount());
    this.flattenFilter(op, operands);
    return operands;
  }

  private void flattenFilter(final NodeOperation op, final List<Node> operands) {
    for (final Node operand : op.getOperands()) {
      if (ExprUtils.isOperation(operand, this.getOperationId())) {
        this.flattenFilter((NodeOperation) operand, operands);
      } else if (!isBoolean(operand)) {
        operands.add(operand);
      }
    }
  }

  private boolean postprocess(final List<Node> operands) {
    if (this.getOperationId() != StandardOperation.AND) {
      return true;
    }

    final EqualityConstraint constraint = filterEqualities(operands);
    if (constraint.isEmpty()) {
      return true;
    }

    final List<Node> reduced = constraint.reduce();
    if (reduced.isEmpty()) { // everything is (eq x x)
      return true;
    }
    if (reduced.size() == 1 && isBoolean(reduced.get(0))) {
      return getBoolean(reduced.get(0));
    }
    operands.addAll(reduced);

    return true;
  }

  private static EqualityConstraint filterEqualities(
      final Collection<? extends Node> operands) {

    final EqualityConstraint constraint = new EqualityConstraint();

    final Iterator<? extends Node> it = operands.iterator();
    while (it.hasNext()) {
      final Node operand = it.next();
      if (ExprUtils.isOperation(operand, StandardOperation.EQ)) {
        constraint.addEquality(operand);
        it.remove();
      } else if (isDistinct(operand)) {
        constraint.addInequality(getDistinct(operand));
        it.remove();
      }
    }
    return constraint;
  }
}
