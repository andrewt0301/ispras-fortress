/*
 * Copyright 2014-2015 ISP RAS (http://www.ispras.ru)
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

/**
 * The ExprTreeVisitorDefault abstract class provides a default implementation for the
 * ExprTreeVisitor interface. This implementation does not perform any actions and does not collect
 * any data. It stores the visitor status, which is by default set to {@code Status.OK} and is
 * accessible via the {@code getStatus} and {@code setStatus} methods. All other methods
 * defined by the {@code ExprTreeVisitor} interface and overridden by the class are empty. The
 * class helps keep the size of other implementations of the {@code ExprTreeVisitor} interface
 * to minimum when it is required to implement only a small number of {@code ExprTreeVisitor}
 * methods to perform some actions on the expression tree being visited.
 * 
 * @author Andrei Tatarnikov
 */

public abstract class ExprTreeVisitorDefault implements ExprTreeVisitor {

  private Status status;

  /**
   * Constructs a default expression tree visitor and sets the visitor status to {@code Status.OK}.
   */

  public ExprTreeVisitorDefault() {
    this.status = Status.OK;
  }

  /**
   * {@inheritDoc}
   */

  @Override
  public final Status getStatus() {
    return status;
  }

  /**
   * Sets the current visitor status.
   * 
   * @param status New visitor status.
   * @throws NullPointerException if the parameter is {@code null}.
   */

  public final void setStatus(Status status) {
    if (null == status)
      throw new NullPointerException();

    this.status = status;
  }

  @Override
  public void onRootBegin() { /* Empty */}

  @Override
  public void onRootEnd() { /* Empty */}

  @Override
  public void onOperationBegin(NodeOperation node) { /* Empty */}

  @Override
  public void onOperationEnd(NodeOperation node) { /* Empty */}

  @Override
  public int[] getOperandOrder() { return null; }

  @Override
  public void onOperandBegin(NodeOperation operation, Node operand, int index) { /* Empty */}

  @Override
  public void onOperandEnd(NodeOperation operation, Node operand, int index) { /* Empty */}

  @Override
  public void onValue(NodeValue value) { /* Empty */}

  @Override
  public void onVariable(NodeVariable variable) { /* Empty */}

  @Override
  public void onBindingBegin(NodeBinding node) { /* Empty */}

  @Override
  public void onBindingListEnd(NodeBinding node) { /* Empty */}

  @Override
  public void onBindingEnd(NodeBinding node) { /* Empty */}

  @Override
  public void onBoundVariableBegin(NodeBinding node, NodeVariable variable, Node value) { /* Empty */}

  @Override
  public void onBoundVariableEnd(NodeBinding node, NodeVariable variable, Node value) { /* Empty */}
}
