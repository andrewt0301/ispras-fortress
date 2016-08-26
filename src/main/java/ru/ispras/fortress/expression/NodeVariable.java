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

import static ru.ispras.fortress.util.InvariantChecks.checkNotNull;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;

/**
 * The NodeVariable class represents a node that refers to a variable which is specified as an
 * attribute of a constraint. The class serves as an adapter to allow Variable objects to be used in
 * an expression tree. The variable is unknown or has a value.
 * 
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public final class NodeVariable extends Node {
  /** Creates a new integer variable. */
  public static NodeVariable newInteger(final String name) {
    return new NodeVariable(name, DataType.INTEGER);
  }

  /** Creates a new real variable. */
  public static NodeVariable newReal(final String name) {
    return new NodeVariable(name, DataType.REAL);
  }

  /** Creates a new string variable. */
  public static NodeVariable newString(final String name) {
    return new NodeVariable(name, DataType.STRING);
  }

  /** Creates a new boolean variable. */
  public static NodeVariable newBoolean(final String name) {
    return new NodeVariable(name, DataType.BOOLEAN);
  }

  /** Creates a new variable of unknown type. */
  public static NodeVariable newUnknown(final String name) {
    return new NodeVariable(name, DataType.UNKNOWN);
  }

  /** Creates a new bit vector variable. */
  public static NodeVariable newBitVector(final String name, final int size) {
    return new NodeVariable(name, DataType.BIT_VECTOR(size));
  }

  private final Variable variable;

  /**
   * Constructs a node for an uninitialized variable of the specified type.
   * The constructed variable does not hold any data and its value is set to {@code null}.
   * 
   * @param name Variable name.
   * @param type Variable type.
   * @throws IllegalArgumentException if any of the arguments is {@code null}.
   */
  public NodeVariable(final String name, final DataType type) {
    this(new Variable(name, type));
  }

  /**
   * Creates a node based on a Variable object.
   * 
   * @param variable A variable node object.
   * @throws IllegalArgumentException if the argument is {@code null}.
   */
  public NodeVariable(final Variable variable) {
    super(Kind.VARIABLE);

    checkNotNull(variable);
    this.variable = variable;
  }

  /**
   * Constructor for making deep copies. The variable field is cloned because the Variable class
   * is mutable.
   * 
   * @param nodeVariable Node variable object to be copied.
   * @throws IllegalArgumentException if the argument is {@code null}.
   */
  private NodeVariable(final NodeVariable nodeVariable) {
    super(nodeVariable);
    this.variable = new Variable(nodeVariable.variable);
  }

  /**
   * {@inheritDoc}
   */
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
    checkNotNull(data);
    variable.setData(data);
  }

  /**
   * Returns an object that stores a data value if any value was assigned to the variable (it is a
   * known variable) or null if it is an unknown variable. The exact type of the object returned by
   * the method depends on the implementation. Please see the
   * {@link ru.ispras.fortress.data.DataTypeId} enumeration for details on internal representation
   * of data objects
   * 
   * @return Object that stores the variable value if it is assigned or null otherwise
   */
  public Object getValue() {
    return variable.getData().getValue();
  }

  /**
   * {@inheritDoc}
   */
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
