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
import ru.ispras.fortress.data.types.bitvector.BitVector;
import ru.ispras.fortress.data.types.datamap.DataMap;
import ru.ispras.fortress.jaxb.JaxbNodeValue;
import ru.ispras.fortress.jaxb.JaxbNodeValueAdapter;
import ru.ispras.fortress.util.InvariantChecks;

import java.math.BigInteger;

import javax.xml.bind.annotation.XmlSeeAlso;
import javax.xml.bind.annotation.adapters.XmlJavaTypeAdapter;

/**
 * The {@code NodeValue} class represents a node that stores a constant value.
 * The class serves as an adapter to allow Data to be used in an expression.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
@XmlSeeAlso(JaxbNodeValue.class)
@XmlJavaTypeAdapter(JaxbNodeValueAdapter.class)
public final class NodeValue extends Node {
  /**
   * Creates a new value node based on an integer value.
   *
   * @param value Integer value.
   * @return New value node.
   */
  public static NodeValue newInteger(final int value) {
    return new NodeValue(Data.newInteger(value));
  }

  /**
   * Creates a new value node based on a {@link BigInteger} value.
   *
   * @param value {@link BigInteger} value.
   * @return New value node.
   *
   * @throws IllegalArgumentException if the parameter equals {@code null}.
   */
  public static NodeValue newInteger(final BigInteger value) {
    return new NodeValue(Data.newInteger(value));
  }

  /**
   * Creates a new value node based on a textual representation of an integer value.
   *
   * @param text String to be parsed.
   * @param radix Radix to be used to parsing.
   * @return New value node.
   *
   * @throws IllegalArgumentException if the {@code text} parameter equals {@code null}.
   * @throws NumberFormatException if failed to parse the string.
   */
  public static NodeValue newInteger(final String text, final int radix) {
    return new NodeValue(Data.newInteger(text, radix));
  }

  /**
   * Creates a new value node based on a double value.
   *
   * @param value Double value.
   * @return New value node.
   */
  public static NodeValue newReal(final double value) {
    return new NodeValue(Data.newReal(value));
  }

  /**
   * Creates a new value node based on a String value.
   *
   * @param value String value.
   * @return New value node.
   *
   * @throws IllegalArgumentException if the parameter equals {@code null}.
   */
  public static NodeValue newString(final String value) {
    return new NodeValue(Data.newString(value));
  }

  /**
   * Creates a new value node based on a boolean value.
   *
   * @param value Boolean value.
   * @return New value node.
   */
  public static NodeValue newBoolean(final boolean value) {
    return new NodeValue(Data.newBoolean(value));
  }

  /**
   * Creates a new value node based on a value of an unknown type.
   *
   * @param value Value of an unknown type.
   * @return New value node.
   */
  public static NodeValue newUnknown(final Object value) {
    return new NodeValue(Data.newUnknown(value));
  }

  /**
   * Creates a new value node based on a bit vector.
   *
   * @param value {@link BitVector} value.
   * @return New value node.
   *
   * @throws IllegalArgumentException if the {@code value} parameter equals {@code null}.
   */
  public static NodeValue newBitVector(final BitVector value) {
    return new NodeValue(Data.newBitVector(value));
  }

  /**
   * Creates a new value node based on a bit vector of the specified size constructed from
   * a textual representation.
   *
   * @param text Textual representation of the bit vector.
   * @param radix Radix to be used for text parsing.
   * @param size Size of the resulting bit vector in bits.
   * @return New value node.
   *
   * @throws IllegalArgumentException if the {@code s} argument is {@code null};
   *         if the {@code size} argument is zero or negative.
   */
  public static NodeValue newBitVector(final String text, final int radix, final int size) {
    return new NodeValue(Data.newBitVector(text, radix, size));
  }

  /**
   * Creates a new value node based on a bit vector of the specified size constructed
   * from the specified integer value.
   *
   * @param value An integer value that represents binary data of the bit vector.
   * @param size The bit vector size (in bits).
   * @return New value node.
   *
   * @throws IllegalArgumentException if the {@code size} argument is zero or negative.
   */
  public static NodeValue newBitVector(final int value, final int size) {
    return new NodeValue(Data.newBitVector(value, size));
  }

  /**
   * Creates a new value node based on a bit vector of the specified size constructed
   * from the specified long value.
   *
   * @param value An long value that represents binary data of the bit vector.
   * @param size The bit vector size (in bits).
   * @return New value node.
   *
   * @throws IllegalArgumentException if the {@code size} argument is zero or negative.
   */
  public static NodeValue newBitVector(final long value, final int size) {
    return new NodeValue(Data.newBitVector(value, size));
  }

  /**
   * Creates a new value node based on a bit vector of the specified size constructed
   * from the specified {@link BigInteger} value.
   *
   * @param value A {@link BigInteger} object that stores binary data for a bit vector.
   * @param size The bit vector size (in bits).
   * @return New value node.
   *
   * @throws IllegalArgumentException if the {@code value} argument equals {@code null}.
   */
  public static NodeValue newBitVector(final BigInteger value, final int size) {
    return new NodeValue(Data.newBitVector(value, size));
  }

  /**
   * Creates a new value node based on a bit vector constructed from the specified boolean value.
   *
   * @param value Boolean value to be converted to a bit vector.
   * @return New value node.
   */
  public static NodeValue newBitVector(final boolean value) {
    return new NodeValue(Data.newBitVector(value));
  }

  /**
   * Creates a new value node of the MAP type from the specified {@link DataMap} object.
   *
   * @param value A {@link DataMap} object.
   * @return A New value node.
   *
   * @throws IllegalArgumentException if the {@code map} parameter equals {@code null}.
   */
  public static NodeValue newMap(final DataMap value) {
    return new NodeValue(Data.newMap(value));
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

    InvariantChecks.checkNotNull(data);
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
    InvariantChecks.checkNotNull(data);
    this.data = data;
  }

  /**
   * Returns an object that stores a data value. The exact type of the object returned
   * by the method depends on the data type.
   *
   * @return An object that store the value of the constant.
   */
  public Object getValue() {
    return data.getValue();
  }

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
   * Returns stored {@link BigInteger} value and throws an exception if the stored value
   * has a different type.
   *
   * @return Stored value represented by a {@link BigInteger}.
   * @throws IllegalStateException if the stored data is not convertible to {@code BigInteger}.
   */
  public BigInteger getInteger() {
    return getData().getInteger();
  }

  /**
   * Returns stored {@link BitVector} value and throws an exception if the stored value
   * has a different type.
   *
   * @return Stored value represented by a {@link BitVector}.
   * @throws IllegalStateException if the stored data is not convertible to {@link BitVector}.
   */
  public BitVector getBitVector() {
    return getData().getBitVector();
  }

  /**
   * Returns stored boolean value and throws an exception if the stored value has a different type.
   *
   * @return Stored value represented by a boolean.
   * @throws IllegalStateException if the stored data is not convertible to {@code Boolean}.
   */
  public boolean getBoolean() {
    return getData().getBoolean();
  }

  /**
   * Returns stored Double value and throws an exception if the stored value has a different type.
   *
   * @return Stored value represented by a Double.
   * @throws IllegalStateException if the stored data is not convertible to {@code Double}.
   */
  public double getReal() {
    return getData().getReal();
  }

  /**
   * Returns stored DataMap value and throws an exception if the stored value has a different type.
   *
   * @return Stored value represented by a {@code DataMap}.
   * @throws IllegalStateException if the stored data is not convertible to {@link DataMap}.
   */
  public DataMap getMap() {
    return getData().getMap();
  }
}
