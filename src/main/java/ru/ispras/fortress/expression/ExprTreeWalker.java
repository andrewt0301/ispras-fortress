/*
 * Copyright 2013-2018 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.expression;

import static ru.ispras.fortress.util.InvariantChecks.checkNotNull;

import ru.ispras.fortress.util.TreeVisitor;
import ru.ispras.fortress.util.TreeVisitor.Status;

/**
 * The {@code ExprTreeWalker} class provides methods that traverse an expression tree
 * and apply a visitor to its nodes. The protocol used for traversal is explained
 * {@linkplain TreeVisitor here}.
 * 
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public final class ExprTreeWalker {
  private final ExprTreeVisitor visitor;

  /**
   * Constructs an ExprTreeWalker object.
   * 
   * @param visitor Visitor to be applied to tree nodes.
   * 
   * @throws IllegalArgumentException if the visitor parameter is null.
   */
  public ExprTreeWalker(final ExprTreeVisitor visitor) {
    checkNotNull(visitor);
    this.visitor = visitor;
  }

  /**
   * Checks whether the current status of the visitor equals the specified status.
   * 
   * @param status Status to be checked for equality with the current status of the visitor.
   * @return {@code true} if the visitor status equals the specified status, or
   *         {@code false} otherwise.
   */
  private boolean isStatus(final Status status) {
    return visitor.getStatus() == status;
  }

  /**
   * Visits a sequence of expression trees. Each node in the sequence is considered a root of an
   * expression tree and the visitor is notified about it by calls to the onRootBegin and onRootEnd
   * methods.
   * 
   * @param trees A sequence of expression trees to be visited.
   * 
   * @throws IllegalArgumentException if the parameter equals null; if any of
   *         the child nodes of the expression nodes in the sequence has a unknown type.
   */
  public void visit(final Iterable<? extends Node> trees) {
    checkNotNull(trees);
    for (final Node tree : trees) {
      visit(tree);
      if (isStatus(Status.ABORT)) {
        return;
      }
    }
  }

  /**
   * Visits the specified expression node. The visited node is considered a root of an expression
   * tree and the visitor is notified about it by calls to the onRootBegin and onRootEnd methods.
   * 
   * @param tree Expression tree to be visited.
   * 
   * @throws IllegalArgumentException if the parameter equals null;
   *         if any of the expression tree nodes has a unknown type.
   */
  public void visit(final Node tree) {
    checkNotNull(tree);

    visitor.onBegin();
    if (isStatus(Status.ABORT)) {
      return;
    }

    if (isStatus(Status.OK)) {
      visitNode(tree);
      if (isStatus(Status.ABORT)) {
        return;
      }
    }

    visitor.onEnd();
  }

  /**
   * Visits the specified node.
   * 
   * @param node Node to be visited.
   * 
   * @throws IllegalArgumentException if the parameter equals null;
   *         if the node or any of its child nodes has a unknown type.
   */
  public void visitNode(final Node node) {
    checkNotNull(node);

    switch (node.getKind()) {
      case VALUE:
        visitValue((NodeValue) node);
        break;

      case VARIABLE:
        visitVariable((NodeVariable) node);
        break;

      case OPERATION:
        visitOperation((NodeOperation) node);
        break;

      case BINDING:
        visitBinding((NodeBinding) node);
        break;

      default:
        throw new IllegalArgumentException(String.format(
          "Unknown node kind: %s.", node.getKind()));
    }
  }

  private void visitOperation(final NodeOperation node) {
    checkNotNull(node);

    visitor.onOperationBegin(node);
    if (isStatus(Status.ABORT)) {
      return;
    }

    if (isStatus(Status.OK)) {
      final int[] order = visitor.getOperandOrder();
      if (order != null && order.length != node.getOperandCount()) {
        throw new IllegalStateException(String.format(
            "Illegal length: %d, expected: %d", order.length, node.getOperandCount()));
      }

      for (int index = 0; index < node.getOperandCount(); index++) {
        final Node operand = node.getOperand(order != null ? order[index] : index);

        visitor.onOperandBegin(node, operand, index);
        if (isStatus(Status.ABORT)) {
          return;
        }

        if (isStatus(Status.OK)) {
          visitNode(operand);
          if (isStatus(Status.ABORT)) {
            return;
          }
        }

        visitor.onOperandEnd(node, operand, index);
        if (isStatus(Status.ABORT)) {
          return;
        }
      }
    }

    visitor.onOperationEnd(node);
  }

  private void visitValue(final NodeValue node) {
    checkNotNull(node);
    visitor.onValue(node);
  }

  private void visitVariable(final NodeVariable node) {
    checkNotNull(node);
    visitor.onVariable(node);
  }

  private void visitBinding(final NodeBinding node) {
    checkNotNull(node);

    visitor.onBindingBegin(node);
    if (isStatus(Status.ABORT)) {
      return;
    }

    if (isStatus(Status.OK)) {
      for (final NodeBinding.BoundVariable bound : node.getBindings()) {
        visitor.onBoundVariableBegin(node, bound.getVariable(), bound.getValue());
        if (isStatus(Status.ABORT)) {
          return;
        }

        if (isStatus(Status.OK)) {
          visitNode(bound.getValue());
          if (isStatus(Status.ABORT)) {
            return;
          }
        }

        visitor.onBoundVariableEnd(node, bound.getVariable(), bound.getValue());
        if (isStatus(Status.ABORT)) {
          return;
        }
      }

      visitor.onBindingListEnd(node);
      if (isStatus(Status.ABORT)) {
        return;
      }

      visitNode(node.getExpression());
      if (isStatus(Status.ABORT)) {
        return;
      }
    }

    visitor.onBindingEnd(node);
  }
}
