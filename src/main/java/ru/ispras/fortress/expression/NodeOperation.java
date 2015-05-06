/*
 * Copyright 2011-2015 ISP RAS (http://www.ispras.ru)
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

import static ru.ispras.fortress.util.InvariantChecks.checkBounds;
import static ru.ispras.fortress.util.InvariantChecks.checkNotNull;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.DataTypeId;

/**
 * The NodeOperation class represents an expression node described by an operation and operands.
 * 
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */

public final class NodeOperation extends Node {
  private final Enum<?> operation;
  private final Node[] operands;
  private DataType dataType;

  /**
   * Creates an operation node that has a variable number of operands (from 0 to infinity).
   * 
   * @param operation Operation identifier.
   * @param operands Operands packed into an array of expression nodes.
   * 
   * @throws IllegalArgumentException if any parameter (including every operand) is {@code null}.
   */

  public <T extends Enum<? extends T>> NodeOperation(
      final T operation,
      final Node ... operands) {
    super(Kind.OPERATION);

    checkNotNull(operation);
    for (final Node operand : operands) {
      checkNotNull(operand);
    }

    this.operation = operation;
    this.operands = operands;
    this.dataType = DataType.UNKNOWN;
  }

  /**
   * Creates an operation node that has a variable number of operands (from 0 to infinity)
   * packed into a collection.
   * 
   * @param operation Operation identifier.
   * @param operands Operands packed into a collection of expression nodes.
   * 
   * @throws IllegalArgumentException if any parameter (including every operand) is {@code null}.
   */

  public <T extends Enum<? extends T>> NodeOperation(
      final T operation,
      final Collection<? extends Node> operands) {
    this(operation, operands != null ? operands.toArray(new Node[operands.size()]) : null);
  }

  /**
   * Constructor for making deep copies. The operation field is immutable and, therefore, it copied
   * by reference. The operands array is cloned because it contains nodes that must be cloned to
   * create a fully independent copy of an expression.
   * 
   * @param node Node operation object to be copied.
   */

  private NodeOperation(final NodeOperation node) {
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

  public Node getOperand(final int index) {
    checkBounds(index, operands.length);
    return operands[index];
  }

  /**
   * Returns an unmodifiable list of operands.
   * 
   * @return An unmodifiable list of operands.
   */

  public List<Node> getOperands() {
    return Collections.unmodifiableList(Arrays.asList(operands));	  
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
    if (operation instanceof TypeRule) {
      final DataType[] types = new DataType[getOperandCount()];

      final int paramCount = StandardOperation.getParameterCount(operation);
      final int[] params = new int[paramCount];

      for (int index = 0, paramIndex = 0; index < getOperandCount(); ++index) {
        final Node operand = getOperand(index);
        types[index] = operand.getDataType();

        if (paramIndex < paramCount) {
          if (Node.Kind.VALUE != operand.getKind()) {
            throw new IllegalStateException(
                "Operand is not a value: " + operand);
          }

          final Data operandData = ((NodeValue) operand).getData();
          if (DataTypeId.LOGIC_INTEGER != operandData.getType().getTypeId()) {
            throw new IllegalStateException(
                "Operand is not a constant integer value: " + operand);
          }

          final BigInteger value = (BigInteger) operandData.getValue();
          if (value.compareTo(BigInteger.valueOf(Integer.MIN_VALUE)) < 0 || 
              value.compareTo(BigInteger.valueOf(Integer.MAX_VALUE)) > 0) {
            throw new IndexOutOfBoundsException(value + " is out of bounds.");
          }

          params[paramIndex] = value.intValue();
          paramIndex++;
        }
      }

      dataType = ((TypeRule) operation).getResultType(types, params);
    }

    return dataType;
  }

  @Override
  public int hashCode() {
    final int prime = 31;
    return prime * operation.hashCode() + Arrays.hashCode(operands);
  }

  @Override
  public boolean equals(final Object obj) {
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

    sb.append('(');
    sb.append(operation.name());

    for (final Node operand : operands) {
      sb.append(' ');
      sb.append(operand.toString());
    }

    sb.append(')');
    return sb.toString();
  }
}
