/*
 * Copyright 2011-2018 ISP RAS (http://www.ispras.ru)
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

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.DataTypeId;
import ru.ispras.fortress.transformer.TypeConversion;
import ru.ispras.fortress.util.InvariantChecks;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

/**
 * The {@link NodeOperation} class represents an expression node described by an operation
 * and operands.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public final class NodeOperation extends Node {
  private final Enum<?> operation;
  private final List<Node> operands;
  private final DataType dataType;

  /**
   * Creates an operation node that has a variable number of operands (from 0 to infinity).
   *
   * @param operation Operation identifier.
   * @param operands Array of expression operands.
   * @param <T> Operation identifier type.
   *
   * @throws IllegalArgumentException if any parameter (including every operand) is {@code null}.
   */
  public <T extends Enum<? extends T>> NodeOperation(
      final T operation,
      final Node... operands) {
    this(operation, null, operands);
  }

  /**
   * Creates an operation node that has a variable number of operands (from 0 to infinity).
   *
   * @param operation Operation identifier.
   * @param operands Array of expression operands.
   * @param dataType Data type associated with the expression or {@code null} to rely
   *        on automated type calculation.
   * @param <T> Operation identifier type.
   *
   * @throws IllegalArgumentException if any parameter (including every operand) is {@code null}.
   */
  public <T extends Enum<? extends T>> NodeOperation(
      final T operation,
      final DataType dataType,
      final Node... operands) {
    this(operation, dataType, operands != null ? Arrays.asList(operands) : null, 0);
  }

  /**
   * Creates an operation node that has a variable number of operands (from 0 to infinity)
   * packed into a collection.
   *
   * @param operation Operation identifier.
   * @param operands Collection of expression operands.
   * @param <T> Operation identifier type.
   *
   * @throws IllegalArgumentException if any parameter (including every operand) is {@code null}.
   */
  public <T extends Enum<? extends T>> NodeOperation(
      final T operation,
      final Collection<? extends Node> operands) {
    this(operation, null, operands);
  }

  /**
   * Creates an operation node that has a variable number of operands (from 0 to infinity)
   * packed into a collection.
   *
   * @param operation Operation identifier.
   * @param dataType Data type associated with the expression or {@code null} to rely
   *        on automated type calculation.
   * @param operands Collection of expression operands.
   * @param <T> Operation identifier type.
   *
   * @throws IllegalArgumentException if any parameter (including every operand) is {@code null}.
   */
  public <T extends Enum<? extends T>> NodeOperation(
      final T operation,
      final DataType dataType,
      final Collection<? extends Node> operands) {
    this(operation, dataType, operands != null ? new ArrayList<>(operands) : null, 0);
  }

  private <T extends Enum<? extends T>> NodeOperation(
      final T operation,
      final DataType dataType,
      final List<Node> operands,
      final int unused) {
    super(Kind.OPERATION);

    InvariantChecks.checkNotNull(operation);
    for (final Node operand : operands) {
      InvariantChecks.checkNotNull(operand);
    }

    this.operation = operation;
    this.dataType = dataType;
    this.operands = Collections.unmodifiableList(operands);
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

    final List<Node> operandCopies = new ArrayList<>(node.operands.size());
    for (final Node operand : node.operands) {
      operandCopies.add(operand.deepCopy());
    }

    this.operation = node.operation;
    this.operands = Collections.unmodifiableList(operandCopies);
    this.dataType = node.dataType;
  }

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
    return operands.size();
  }

  /**
   * Returns an operand by its index.
   *
   * @param index Index of the operand.
   * @return An operand of the expression.
   */
  public Node getOperand(final int index) {
    InvariantChecks.checkBounds(index, operands.size());
    return operands.get(index);
  }

  /**
   * Returns an unmodifiable list of operands.
   *
   * @return An unmodifiable list of operands.
   */
  public List<Node> getOperands() {
    return operands;
  }

  /**
   * Returns an operation identifier.
   *
   * @return An operation identifier.
   */
  public Enum<?> getOperationId() {
    return operation;
  }

  @Override
  public DataType getDataType() {
    if (null != dataType) {
      return dataType;
    }

    if (operation instanceof TypeRule) {
      return ((TypeRule) operation).getResultType(
          getOperandDataTypes(), getParams());
    }

    return DataType.UNKNOWN;
  }

  @Override
  public int hashCode() {
    final int prime = 31;
    return prime * operation.hashCode() + operands.hashCode();
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
    return operation.equals(other.operation) && operands.equals(other.operands);
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

  private DataType[] getOperandDataTypes() {
    final DataType[] types = new DataType[getOperandCount()];

    for (int index = 0; index < operands.size(); ++index) {
      final Node operand = operands.get(index);
      types[index] = operand.getDataType();
    }

    return types;
  }

  private int[] getParams() {
    final int paramCount = StandardOperation.getParameterCount(operation);
    final int[] params = new int[paramCount];

    if (paramCount == 0) {
      return params;
    }

    /* If parameters are non-constant but equal, treat them as zeros. */
    final Node firstParam = operands.get(0);

    if (Kind.VALUE != firstParam.getKind()
        && (getOperationId() == StandardOperation.BVEXTRACT
          || getOperationId() == StandardOperation.SELECT)) {

      boolean equalParams = true;

      for (int index = 0; index < paramCount; index++) {

        final Node param = operands.get(index);
        if (Kind.VALUE != param.getKind() && !param.equals(firstParam)) {
          equalParams = false;
          break;
        }
      }

      if (equalParams) {
        Arrays.fill(params, 0);
        return params;
      }
    }

    for (int index = 0; index < paramCount; ++index) {

      final Node operand = operands.get(index);

      if (Node.Kind.VALUE != operand.getKind()) {

        return params;
        /*throw new IllegalStateException(
            "Parameter is not a value: " + operand);*/
      }

      Data data = ((NodeValue) operand).getData();
      if (!data.isType(DataTypeId.LOGIC_INTEGER)) {

        final Node toInt = TypeConversion.coerce(operand, DataType.INTEGER);

        if (toInt == null || Kind.VALUE != toInt.getKind()) {
          throw new IllegalStateException(
              "Can't cast parameter to a constant integer value: " + operand);
        }
        data = ((NodeValue)toInt).getData();
      }

      final BigInteger value = (BigInteger) data.getValue();
      if (value.compareTo(BigInteger.valueOf(Integer.MIN_VALUE)) < 0
          || value.compareTo(BigInteger.valueOf(Integer.MAX_VALUE)) > 0) {
        throw new IndexOutOfBoundsException(value + " is out of bounds.");
      }

      params[index] = value.intValue();
    }

    return params;
  }
}
