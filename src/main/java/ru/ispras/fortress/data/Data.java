/*
 * Copyright 2012-2015 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.data;

import static ru.ispras.fortress.util.InvariantChecks.checkNotNull;

import java.math.BigInteger;
import ru.ispras.fortress.data.types.bitvector.BitVector;
import ru.ispras.fortress.data.types.datamap.DataMap;

/**
 * The Data class is a storage of data being processed. This data will be used as an input or an
 * output parameter of a constraint solver.
 * 
 * @author Andrei Tatarnikov
 */

public final class Data {
  private final DataType type;
  private final Object value;
  private Object userData;

  /**
   * Creates a data object of the INTEGER type from a BigInteger value.
   * 
   * @param value A BitInteger value.
   * @return New data object.
   * 
   * @throws NullPointerException if the parameter equals {@code null}.
   */

  public static Data newInteger(BigInteger value) {
    checkNotNull(value);
    return new Data(DataType.INTEGER, value);
  }

  /**
   * Creates a data object of the INTEGER type from a long value.
   * 
   * @param value A long value.
   * @return New data object.
   */

  public static Data newInteger(long value) {
    return newInteger(BigInteger.valueOf(value));
  }

  /**
   * Creates a data object of the INTEGER type from an integer value.
   * 
   * @param value An integer value.
   * @return New data object.
   */

  public static Data newInteger(int value) {
    return newInteger((long) value);
  }

  /**
   * Creates a data object of the INTEGER type from a string.
   * 
   * @param text String to be parsed.
   * @param radix Radix to be used for parsing. 
   * @return New data object.
   * 
   * @throws NullPointerException if the {@code text} parameter equals {@code null}.
   * @throws NumberFormatException if failed to parse the string. 
   */

  public static Data newInteger(String text, int radix) {
    checkNotNull(text);
    return newInteger(new BigInteger(text, radix));
  }

  /**
   * Creates a data object of the REAL type from an double value.
   * 
   * @param value A double value.
   * @return An new data object.
   */

  public static Data newReal(double value) {
    return new Data(DataType.REAL, value);
  }

  /**
   * A boolean constant for a {@code true} value. Defined as private to avoid incorrect results
   * when objects are tested for equality because the implementation cannot guarantee it is a
   * singleton (the Data constructor is public and the DataType.valueOf method uses it to create new
   * instances).
   */

  private static final Data TRUE = new Data(DataType.BOOLEAN, true);

  /**
   * A boolean constant for a {@code false} value. Defined as private to avoid incorrect
   * results when objects are tested for equality because the implementation cannot guarantee it is
   * a singleton (the Data constructor is public and the DataType.valueOf method uses it to create
   * new instances).
   */

  private static final Data FALSE = new Data(DataType.BOOLEAN, false);

  /**
   * Creates a data object of the BOOLEAN type from a boolean value.
   * 
   * @param value A boolean value.
   * @return A new data object.
   */

  public static Data newBoolean(boolean value) {
    return value ? TRUE : FALSE;
  }

  /**
   * Creates a data object from an object value of an unknown type (UNKNOWN will be used as target
   * type). Method for wrapping uninterpreted data that should not be passed to the solver.
   * 
   * @param value A value of an unknown type.
   * @return New data object.
   */

  public static Data newUnknown(Object value) {
    return new Data(DataType.UNKNOWN, value);
  }

  /**
   * Creates a data object of the BIT_VECTOR type from a BigInteger object.
   * 
   * @param value A BigInteger object that stores binary data for a bit vector.
   * @param size The bit vector size (in bits).
   * @return A new data object.
   * 
   * @throws NullPointerException if the {@code value} parameter equals {@code null}.
   */

  public static Data newBitVector(BigInteger value, int size) {
    checkNotNull(value);

    final DataType dt = DataType.BIT_VECTOR(size);
    final Object v = BitVector.unmodifiable(BitVector.valueOf(value, size));

    return new Data(dt, v);
  }

  /**
   * Creates a data object of the BIT_VECTOR type from a BitVector object.
   * 
   * @param value A BitVector object.
   * @return A new data object.
   * 
   * @throws NullPointerException if the {@code value} parameter equals {@code null}.
   */

  public static Data newBitVector(BitVector value) {
    checkNotNull(value);

    final DataType dt = DataType.BIT_VECTOR(value.getBitSize());
    final Object v = BitVector.unmodifiable(value);

    return new Data(dt, v);
  }

  /**
   * Creates a data object of the BIT_VECTOR type from a string.
   * 
   * @param s Textual representation of the bit vector.
   * @param radix Radix to be used for parsing.
   * @param size Size of the resulting bit vector in bits.
   * @return A new data object.
   * 
   * @throws NullPointerException if the {@code s} parameter equals {@code null}.
   */

  public static Data newBitVector(String s, int radix, int size) {
    checkNotNull(s);

    final DataType dt = DataType.BIT_VECTOR(size);
    final Object v = BitVector.unmodifiable(BitVector.valueOf(s, radix, size));

    return new Data(dt, v);
  }

  /**
   * Creates a data object of the BIT_VECTOR type from an integer value.
   * 
   * @param value Integer value to be converted.
   * @param size The bit vector size (in bits).
   * @return A new data object.
   */

  public static Data newBitVector(int value, int size) {
    return newBitVector((long) value, size);
  }

  /**
   * Creates a data object of the BIT_VECTOR type from a long integer value.
   * 
   * @param value Long integer value to be converted.
   * @param size The bit vector size (in bits).
   * @return A new data object.
   */

  public static Data newBitVector(long value, int size) {
    final DataType dt = DataType.BIT_VECTOR(size);
    final Object v = BitVector.unmodifiable(BitVector.valueOf(value, size));

    return new Data(dt, v);
  }

  /**
   * Creates a data object of the MAP type from the specified {@link DataMap} object.
   * 
   * @param map A {@link DataMap} object.
   * @return A new data object.
   * 
   * @throws NullPointerException if the {@code map} parameter equals {@code null}.
   */

  public static Data newArray(DataMap map) {
    checkNotNull(map);
    return new Data(DataType.MAP(
        map.getKeyType(), map.getValueType()), map.copy());
  }

  /**
   * Constructs a data object of the specified type and initializes its value with the specified
   * value object.
   * 
   * @param type The type of the data.
   * @param value An object of related type that stores the data.
   */

  public Data(DataType type, Object value) {
    checkNotNull(type);

    if (null != value && !type.getValueClass().isAssignableFrom(value.getClass())) {
      throw new IllegalArgumentException(String.format(
        "%s is illegal value type, %s is expected.",
        value.getClass().getSimpleName(), type.getValueClass().getSimpleName()));
    }

    this.type = type;
    this.value = value;
    this.userData = null;
  }

  /**
   * Returns information about the type of the stored value.
   * 
   * @return An IDataType object.
   */

  public DataType getType() {
    return type;
  }

  /**
   * Checks whether a value assigned to the the data object.
   * 
   * @return true if a value is assigned or false otherwise.
   */

  public boolean hasValue() {
    return null != getValue();
  }

  /**
   * Returns an object that holds the data.
   * 
   * @return A type-dependent object that stores the data.
   */

  public Object getValue() {
    return value;
  }

  /**
   * Returns the value of the used-defined property.
   * 
   * @return User-defined object.
   */

  public Object getUserData() {
    return userData;
  }

  /**
   * Assigns value to the user-defined property.
   * 
   * @param obj User-defined object.
   */

  public void setUserData(Object obj) {
    this.userData = obj;
  }

  @Override
  public int hashCode() {
    final int prime = 31;
    return prime * type.hashCode() + ((value == null) ? 0 : value.hashCode());
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

    final Data other = (Data) obj;
    if (!type.equals(other.type)) {
      return false;
    }

    if (value == null) {
      return (null == other.value);
    }

    return value.equals(other.value);
  }

  @Override
  public String toString() {
    return String.format("Data[type=%s, value=%s]",
      type.toString(), null == value ? "uninitialized" : value.toString());
  }
}
