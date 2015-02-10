/*
 * Copyright 2013-2015 ISP RAS (http://www.ispras.ru)
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

import ru.ispras.fortress.expression.ExprTreeVisitor.Status;

/**
 * The ExprTreeWalker class provides methods that traverse an expression tree and apply a visitor to
 * its nodes.
 * 
 * <p>
 * NOTE: Actions taken in the traversal process depend on the current status of the visitor (see
 * {@link Status}). There are three possible statuses:
 * <ol>
 * <li>OK - continue traversal
 * <li>SKIP - skip child nodes
 * <li>ABORT - stop traversal
 * </ol>
 * 
 * <p>
 * The status is checked after calling any visitor method. Once ABORT is set, all traversal methods
 * return. If after a call to a method having the Begin suffix (e.g. onExprBegin), the SKIP status
 * is set (not ABORT and not OR), nested elements of the visited node (child nodes or subtrees) are
 * not traversed and a corresponding terminating method (that has the End suffix) is called.
 * 
 * @author Andrei Tatarnikov
 */

public final class ExprTreeWalker {
  private final ExprTreeVisitor visitor;

  /**
   * Constructs an ExprTreeWalker object.
   * 
   * @param visitor Visitor to be applied to tree nodes.
   * 
   * @throws NullPointerException if the visitor parameter is null.
   */

  public ExprTreeWalker(ExprTreeVisitor visitor) {
    checkNotNull(visitor);
    this.visitor = visitor;
  }

  /**
   * Checks whether the current status of the visitor equals the specified status.
   * 
   * @param status Status to be checked for equality with the current status of the visitor.
   * @return <code>true</code> if the visitor status equals the specified status, or
   *         <code>false</code> otherwise.
   */

  private boolean isStatus(Status status) {
    return visitor.getStatus() == status;
  }

  /**
   * Visits a sequence of expression trees. Each node in the sequence is considered a root of an
   * expression tree and the visitor is notified about it by calls to the onRootBegin and onRootEnd
   * methods.
   * 
   * @param trees A sequence of expression trees to be visited.
   * 
   * @throws NullPointerException if the parameter equals null. IllegalArgumentException if any of
   *         the child nodes of the expression nodes in the sequence has a unknown type.
   */

  public void visit(Iterable<? extends Node> trees) {
    checkNotNull(trees);
    for (Node tree : trees) {
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
   * @throws NullPointerException if the parameter equals null.
   * @throws IllegalArgumentException if any of the expression tree nodes has a unknown type.
   */

  public void visit(Node tree) {
    checkNotNull(tree);

    visitor.onRootBegin();
    if (isStatus(Status.ABORT)) {
      return;
    }

    if (isStatus(Status.OK)) {
      visitNode(tree);
      if (isStatus(Status.ABORT)) {
        return;
      }
    }

    visitor.onRootEnd();
  }

  /**
   * Visits the specified node.
   * 
   * @param node Node to be visited.
   * 
   * @throws NullPointerException if the parameter equals null.
   * @throws IllegalArgumentException if the node or any of its child nodes has a unknown type.
   */

  public void visitNode(Node node) {
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

  private void visitOperation(NodeOperation node) {
    checkNotNull(node);

    visitor.onOperationBegin(node);
    if (isStatus(Status.ABORT)) {
      return;
    }

    if (isStatus(Status.OK)) {
      final int order[] = visitor.getOperandOrder();
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

  private void visitValue(NodeValue node) {
    checkNotNull(node);
    visitor.onValue(node);
  }

  private void visitVariable(NodeVariable node) {
    checkNotNull(node);
    visitor.onVariable(node);
  }

  private void visitBinding(NodeBinding node) {
    checkNotNull(node);

    visitor.onBindingBegin(node);
    if (isStatus(Status.ABORT)) {
      return;
    }

    if (isStatus(Status.OK)) {
      for (NodeBinding.BoundVariable bound : node.getBindings()) {
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
