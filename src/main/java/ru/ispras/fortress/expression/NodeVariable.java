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
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.util.InvariantChecks;
import ru.ispras.fortress.util.Value;

/**
 * The {@link NodeVariable} class represents a node that refers to a variable which is specified
 * as an attribute of a constraint. The class serves as an adapter to allow {@link Variable}
 * objects to be used in an expression tree. The variable is unknown or has a value.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public final class NodeVariable extends Node {
  /**
   * Creates a new integer variable.
   *
   * @param name Variable name.
   * @return New variable node.
   *
   * @throws IllegalArgumentException if the argument is {@code null}.
   */
  public static NodeVariable newInteger(final String name) {
    return new NodeVariable(name, DataType.INTEGER);
  }

  /**
   * Creates a new real variable.
   *
   * @param name Variable name.
   * @return New variable node.
   *
   * @throws IllegalArgumentException if the argument is {@code null}.
   */
  public static NodeVariable newReal(final String name) {
    return new NodeVariable(name, DataType.REAL);
  }

  /**
   * Creates a new string variable.
   *
   * @param name Variable name.
   * @return New variable node.
   *
   * @throws IllegalArgumentException if the argument is {@code null}.
   */
  public static NodeVariable newString(final String name) {
    return new NodeVariable(name, DataType.STRING);
  }

  /**
   * Creates a new boolean variable.
   *
   * @param name Variable name.
   * @return New variable node.
   *
   * @throws IllegalArgumentException if the argument is {@code null}.
   */
  public static NodeVariable newBoolean(final String name) {
    return new NodeVariable(name, DataType.BOOLEAN);
  }

  /**
   * Creates a new variable of unknown type.
   *
   * @param name Variable name.
   * @return New variable node.
   *
   * @throws IllegalArgumentException if the argument is {@code null}.
   */
  public static NodeVariable newUnknown(final String name) {
    return new NodeVariable(name, DataType.UNKNOWN);
  }

  /**
   * Creates a new bit vector variable.
   *
   * @param name Variable name.
   * @param size Bit vector size in bits.
   * @return New variable node.
   *
   * @throws IllegalArgumentException if the {@code name} argument is {@code null} or
   *         if the {@code size} argument is {@code <= 0}.
   */
  public static NodeVariable newBitVector(final String name, final int size) {
    return new NodeVariable(name, DataType.bitVector(size));
  }

  /**
   * Creates a map-based variable.
   *
   * @param name Variable name.
   * @param keyType Key type.
   * @param valueType Value type.
   * @return New variable node.
   *
   * @throws IllegalArgumentException if any of the arguments is {@code null}.
   */
  public static NodeVariable newMap(
      final String name, final DataType keyType, final DataType valueType) {
    return new NodeVariable(name, DataType.map(keyType, valueType));
  }

  private final Variable variable;

  /**
   * Constructs a node variable from its name and associated dynamic data.
   * Used for creating context-dependent variables.
   *
   * @param name Variable name.
   * @param data Dynamic value.
   *
   * @throws IllegalArgumentException if any of the arguments is {@code null}.
   */
  public NodeVariable(final String name, final Value<Data> data) {
    this(new Variable(name, data));
  }

  /**
   * Constructs a node for an uninitialized variable of the specified type.
   * The constructed variable does not hold any data and its value is set to {@code null}.
   *
   * @param name Variable name.
   * @param type Variable type.
   *
   * @throws IllegalArgumentException if any of the arguments is {@code null}.
   */
  public NodeVariable(final String name, final DataType type) {
    this(new Variable(name, type));
  }

  /**
   * Constructs a node for a variable that holds the specified value.
   *
   * @param name Variable name.
   * @param value Variable value.
   *
   * @throws IllegalArgumentException if any of the arguments is {@code null}.
   */
  public NodeVariable(final String name, final Data value) {
    this(new Variable(name, value));
  }

  /**
   * Creates a node based on a {@link Variable} object.
   *
   * @param variable A variable node object.
   *
   * @throws IllegalArgumentException if the argument is {@code null}.
   */
  public NodeVariable(final Variable variable) {
    super(Kind.VARIABLE);

    InvariantChecks.checkNotNull(variable);
    this.variable = variable;
  }

  /**
   * Constructor for making deep copies. The variable field is cloned because
   * the {@link Variable} class is mutable.
   *
   * @param nodeVariable Node variable object to be copied.
   *
   * @throws IllegalArgumentException if the argument is {@code null}.
   */
  private NodeVariable(final NodeVariable nodeVariable) {
    super(nodeVariable);
    this.variable = new Variable(nodeVariable.variable);
  }

  @Override
  public Node deepCopy() {
    return new NodeVariable(this);
  }

  /**
   * Returns the variable associated with the node.
   *
   * @return Variable associated with the node.
   */
  public Variable getVariable() {
    return variable;
  }

  /**
   * Returns the name of the variable.
   *
   * @return The variable name.
   */
  public String getName() {
    return variable.getName();
  }

  /**
   * Returns the data object that encapsulates the variable value.
   *
   * @return A data object.
   */
  public Data getData() {
    return variable.getData();
  }

  /**
   * Assigns new data value to the variable.
   *
   * @param data Data value to be assigned to the variable.
   *
   * @throws IllegalArgumentException if the argument is {@code null}.
   */
  public void setData(final Data data) {
    InvariantChecks.checkNotNull(data);
    variable.setData(data);
  }

  /**
   * Returns an object that stores a data value if any value was assigned to the variable
   * (it is a known variable) or null if it is an unknown variable. The exact type of the object
   * returned by the method depends on the implementation.
   * Please see the {@link ru.ispras.fortress.data.DataTypeId} enumeration for details on
   * internal representation of data objects
   *
   * @return Object that stores the variable value if it is assigned or null otherwise
   */
  public Object getValue() {
    return variable.getData().getValue();
  }

  @Override
  public DataType getDataType() {
    return variable.getType();
  }

  @Override
  public int hashCode() {
    return variable.hashCode();
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

    final NodeVariable other = (NodeVariable) obj;
    return variable.equals(other.variable);
  }

  @Override
  public String toString() {
    return variable.hasValue() ? variable.getData().getValue().toString() : variable.getName();
  }
}
