/*
 * Copyright 2011-2014 ISP RAS (http://www.ispras.ru)
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

import java.util.Arrays;

import ru.ispras.fortress.data.DataType;

/**
 * The NodeOperation class represents an expression node described by an operation and operands.
 * 
 * @author Andrei Tatarnikov
 */

public final class NodeOperation extends Node {
  private final Enum<?> operation;
  private final Node[] operands;
  private DataType dataType;

  /**
   * Creates an operation node that has a variable number of operands (from 0 to infinity).
   * 
   * @param operation Operation identifier.
   * @param operands Operands packed into an array of syntax elements.
   */

  public <T extends Enum<? extends T>> NodeOperation(T operation, Node... operands) {
    super(Kind.OPERATION);

    if (null == operation) {
      throw new NullPointerException();
    }

    this.operation = operation;
    this.operands = operands;
    this.dataType = DataType.UNKNOWN;
  }

  /**
   * Constructor for making deep copies. The operation field is immutable and, therefore, it copied
   * by reference. The operands array is cloned because it contains nodes that must be cloned to
   * create a fully independent copy of an expression.
   * 
   * @param node Node operation object to be copied.
   */

  private NodeOperation(NodeOperation node) {
    super(node);

    this.operation = node.operation;
    this.operands = new Node[node.operands.length];

    for (int index = 0; index < node.operands.length; index++) {
      this.operands[index] = node.operands[index].deepCopy();
    }

    this.dataType = node.dataType;
  }

  /**
   * {@inheritDoc}
   */

  @Override
  public Node deepCopy() {
    return new NodeOperation(this);
  }

  /**
   * Returns the number of operands.
   * 
   * @return Number of operands.
   */

  public int getOperandCount() {
    return operands.length;
  }

  /**
   * Returns an operand by its index.
   * 
   * @param index Index of the operand.
   * @return An operand of the expression.
   */

  public Node getOperand(int index) {
    if (!((0 <= index) && (index < operands.length))) {
      throw new IndexOutOfBoundsException();
    }

    return operands[index];
  }

  /**
   * Returns an operation identifier.
   * 
   * @return An operation identifier.
   */

  public Enum<?> getOperationId() {
    return operation;
  }

  /**
   * {@inheritDoc}
   */

  @Override
  public DataType getDataType() {
    if (dataType.equals(DataType.UNKNOWN) && operation instanceof TypeRule) {
      final DataType[] types = new DataType[getOperandCount()];

      for (int index = 0; index < getOperandCount(); ++index) {
        types[index] = getOperand(index).getDataType();
      }

      dataType = ((TypeRule) operation).getResultType(types);
    }

    return dataType;
  }

  @Override
  public int hashCode() {
    final int prime = 31;
    return prime * operation.hashCode() + Arrays.hashCode(operands);
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }

    if (obj == null) {
      return false;
    }

    if (getClass() != obj.getClass()) {
      return false;
    }

    final NodeOperation other = (NodeOperation) obj;
    return operation.equals(other.operation) && Arrays.equals(operands, other.operands);
  }

  @Override
  public String toString() {
    final StringBuilder sb = new StringBuilder();

    sb.append("(");
    sb.append(operation.name());

    for (Node operand : operands) {
      sb.append(" ");
      sb.append(operand.toString());
    }

    sb.append(")");
    return sb.toString();
  }
}
