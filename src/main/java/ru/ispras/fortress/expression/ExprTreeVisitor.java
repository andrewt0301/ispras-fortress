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

import ru.ispras.fortress.util.TreeVisitor;

/**
 * Interface to be implemented by all visitor objects applied to an expression tree to collect
 * information or to build another representation of the expression.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public interface ExprTreeVisitor extends TreeVisitor {
  /**
   * Starts visiting an operation node.
   *
   * @param node Operation node.
   */
  void onOperationBegin(NodeOperation node);

  /**
   * Finishes visiting an operation node.
   *
   * @param node Operation node.
   */
  void onOperationEnd(NodeOperation node);

  /**
   * Returns an array of operand indexes that specify in which order the operands of
   * the currently visited operator should be visited. If the order is standard
   * (i.e. [0..N-1]), {@code null} is returned.
   *
   * @return Array of operand indexes or {@code null} for the standard order.
   */
  int[] getOperandOrder();

  /**
   * Notifies that visiting an expression operand has started.
   *
   * @param operation Operation node.
   * @param operand Operand node.
   * @param index Operand index.
   */
  void onOperandBegin(NodeOperation operation, Node operand, int index);

  /**
   * Notifies that visiting an expression operand has finished.
   *
   * @param operation Operation node.
   * @param operand Operand node.
   * @param index Operand index.
   */
  void onOperandEnd(NodeOperation operation, Node operand, int index);

  /**
   * Notifies that a value node has been visited.
   *
   * @param value Value node.
   */
  void onValue(NodeValue value);

  /**
   * Notifies that a variable node has been visited.
   *
   * @param variable Variable node.
   */
  void onVariable(NodeVariable variable);

  /**
   * Starts visiting a binding node.
   *
   * @param node Binding node.
   */
  void onBindingBegin(NodeBinding node);

  /**
   * Notifies that visiting a bound variables list finished.
   *
   * @param node Bounding node.
   */
  void onBindingListEnd(NodeBinding node);

  /**
   * Finishes visiting a binding node.
   *
   * @param node Binding node.
   */
  void onBindingEnd(NodeBinding node);

  /**
   * Notifies that visiting a bound variable has started. Bound value expression will be visited
   * next as general expression.
   * <p>Bound variables are not visited at all.</p>
   *
   * @param node Binding node.
   * @param variable Bound variable reference.
   * @param value Bound value expression.
   */
  void onBoundVariableBegin(NodeBinding node, NodeVariable variable, Node value);

  /**
   * Notifies that visiting a bound variable has finished.
   *
   * @param node Binding node.
   * @param variable Bound variable reference.
   * @param value Bound value expression.
   */
  void onBoundVariableEnd(NodeBinding node, NodeVariable variable, Node value);
}
