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

import java.math.BigInteger;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.types.bitvector.BitVector;
import ru.ispras.fortress.data.types.datamap.DataMap;

/**
 * The NodeValue class represents a node that stores a constant value. The class serves as an
 * adapter to allow Data to be used in an expression.
 * 
 * @author Andrei Tatarnikov
 */

public final class NodeValue extends Node {
  /** Creates a new value node based on an integer value. */
  public static NodeValue newInteger(final int value) {
    return new NodeValue(Data.newInteger(value));
  }

  /** Creates a new value node based on a textual representation of an integer value. */
  public static NodeValue newInteger(final String text, final int radix) {
    return new NodeValue(Data.newInteger(text, radix));
  }

  /** Creates a new value node based on a double value. */
  public static NodeValue newReal(final double value) {
    return new NodeValue(Data.newReal(value));
  }

  /** Creates a new value node based on a boolean value. */
  public static NodeValue newBoolean(final boolean value) {
    return new NodeValue(Data.newBoolean(value));
  }

  /** Creates a new value node based on a value of an unknown type. */
  public static NodeValue newUnknown(final Object value) {
    return new NodeValue(Data.newUnknown(value));
  }

  /** Creates a new value node based on a bit vector. */
  public static NodeValue newBitVector(final BitVector value) {
    return new NodeValue(Data.newBitVector(value));
  }

  private Data data;

  /**
   * Creates a value syntax element based on a data object.
   * 
   * @param data A data object.
   * 
   * @throws IllegalArgumentException if the argument is {@code null}.
   */

  public NodeValue(final Data data) {
    super(Kind.VALUE);

    checkNotNull(data);
    this.data = data;
  }

  /**
   * Constructor for making deep copies. The data field is copied by reference because the Data
   * class guarantees immutability.
   * 
   * @param nodeValue Node value object to be copied.
   */

  private NodeValue(final NodeValue nodeValue) {
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
   * @throws IllegalArgumentException if the argument is {@code null}. 
   */

  public void setData(final Data data) {
    checkNotNull(data);
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

    final NodeValue other = (NodeValue) obj;
    return data.equals(other.data);
  }
  
  @Override
  public String toString() {
    return data.getValue().toString();
  }

  /**
   * Returns stored BigInteger value and throws an exception if the stored value has a different type.
   */

  public BigInteger getInteger() {
    return getData().getInteger();
  }

  /**
   * Returns stored BitVector value and throws an exception if the stored value has a different type.
   */

  public BitVector getBitVector() {
    return getData().getBitVector();
  }

  /**
   * Returns stored boolean value and throws an exception if the stored value has a different type.
   */

  public boolean getBoolean() {
    return getData().getBoolean();
  }

  /**
   * Returns stored Double value and throws an exception if the stored value has a different type.
   */

  public double getReal() {
    return getData().getReal();
  }

  /**
   * Returns stored DataMap value and throws an exception if the stored value has a different type.
   */

  public DataMap getArray() {
    return getData().getArray();
  }
}
