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

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.types.bitvector.BitVector;

/**
 * The NodeValue class represents a node that stores a constant value. The class serves as an
 * adapter to allow Data to be used in an expression.
 * 
 * @author Andrei Tatarnikov
 */

public final class NodeValue extends Node {
  /** Creates a new value node based on an integer value. */
  public static NodeValue newInteger(int value) {
    return new NodeValue(Data.newInteger(value));
  }

  /** Creates a new value node based on a double value. */
  public static NodeValue newReal(double value) {
    return new NodeValue(Data.newReal(value));
  }

  /** Creates a new value node based on a boolean value. */
  public static NodeValue newBoolean(boolean value) {
    return new NodeValue(Data.newBoolean(value));
  }

  /** Creates a new value node based on a value of an unknown type. */
  public static NodeValue newUnknown(Object value) {
    return new NodeValue(Data.newUnknown(value));
  }

  /** Creates a new value node based on a bit vector. */
  public static NodeValue newBitVector(BitVector value) {
    return new NodeValue(Data.newBitVector(value));
  }

  private Data data;

  /**
   * Creates a value syntax element based on a data object.
   * 
   * @param data A data object.
   */

  public NodeValue(Data data) {
    super(Kind.VALUE);

    if (null == data) {
      throw new NullPointerException();
    }

    this.data = data;
  }

  /**
   * Constructor for making deep copies. The data field is copied by reference because the Data
   * class guarantees immutablility.
   * 
   * @param nodeValue Node value object to be copied.
   */

  private NodeValue(NodeValue nodeValue) {
    super(nodeValue);
    this.data = nodeValue.data;
  }

  /**
   * {@inheritDoc}
   */

  @Override
  public Node deepCopy() {
    return new NodeValue(this);
  }

  /**
   * Returns the data object that encapsulates the value.
   * 
   * @return A data object.
   */

  public Data getData() {
    return data;
  }

  /**
   * Changes the data value associated with the node. 
   * 
   * @param data New data value to be associated with the node.
   * 
   * @throws NullPointerException if the argument is {@code null}. 
   */

  public void setData(Data data) {
    if (null == data) {
      throw new NullPointerException();
    }
    
    this.data = data;
  }

  /**
   * Returns an object that stores a data value. The exact type of the object returned by the method
   * depends on the data type.
   * 
   * @return An object that store the value of the constant.
   */

  public Object getValue() {
    return data.getValue();
  }

  /**
   * {@inheritDoc}
   */

  @Override
  public DataType getDataType() {
    return data.getType();
  }

  @Override
  public int hashCode() {
    return data.hashCode();
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

    final NodeValue other = (NodeValue) obj;
    return data.equals(other.data);
  }

  @Override
  public String toString() {
    return data.getValue().toString();
  }
}
