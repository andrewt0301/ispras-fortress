/*
 * Copyright 2012-2018 ISP RAS (http://www.ispras.ru)
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

import ru.ispras.fortress.data.types.bitvector.BitVector;
import ru.ispras.fortress.data.types.datamap.DataMap;
import ru.ispras.fortress.util.InvariantChecks;

import java.math.BigInteger;

/**
 * The {@link Data} class is a storage of data being processed. This data will be used as
 * an input or an output parameter of a constraint solver.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public final class Data {
  private final DataType type;
  private final Object value;
  private Object userData;

  /**
   * Creates a data object of the INTEGER type from a {@link BigInteger} value.
   *
   * @param value A BitInteger value.
   * @return New data object.
   *
   * @throws IllegalArgumentException if the parameter equals {@code null}.
   */
  public static Data newInteger(final BigInteger value) {
    InvariantChecks.checkNotNull(value);
    return new Data(DataType.INTEGER, value);
  }

  /**
   * Creates a data object of the INTEGER type from a long value.
   *
   * @param value A long value.
   * @return New data object.
   */
  public static Data newInteger(final long value) {
    return newInteger(BigInteger.valueOf(value));
  }

  /**
   * Creates a data object of the INTEGER type from an integer value.
   * 
   * @param value An integer value.
   * @return New data object.
   */
  public static Data newInteger(final int value) {
    return newInteger((long) value);
  }

  /**
   * Creates a data object of the INTEGER type from a string.
   *
   * @param text String to be parsed.
   * @param radix Radix to be used for parsing.
   * @return New data object.
   *
   * @throws IllegalArgumentException if the {@code text} parameter equals {@code null}.
   * @throws NumberFormatException if failed to parse the string. 
   */
  public static Data newInteger(final String text, final int radix) {
    InvariantChecks.checkNotNull(text);
    return newInteger(new BigInteger(text, radix));
  }

  /**
   * Creates a data object of the REAL type from an double value.
   *
   * @param value A double value.
   * @return An new data object.
   */
  public static Data newReal(final double value) {
    return new Data(DataType.REAL, value);
  }

  /**
   * Creates a data object of the STRING type from a String value.
   *
   * @param value A String value.
   * @return An new data object.
   *
   * @throws IllegalArgumentException if the parameter equals {@code null}.
   */
  public static Data newString(final String value) {
    InvariantChecks.checkNotNull(value);
    return new Data(DataType.STRING, value);
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
  public static Data newBoolean(final boolean value) {
    return value ? TRUE : FALSE;
  }

  /**
   * Creates a data object from an object value of an unknown type (UNKNOWN will be used as target
   * type). Method for wrapping uninterpreted data that should not be passed to the solver.
   *
   * @param value A value of an unknown type.
   * @return New data object.
   */
  public static Data newUnknown(final Object value) {
    return new Data(DataType.UNKNOWN, value);
  }

  /**
   * Creates a data object of the BIT_VECTOR type from a BigInteger object.
   *
   * @param value A BigInteger object that stores binary data for a bit vector.
   * @param size The bit vector size (in bits).
   * @return A new data object.
   *
   * @throws IllegalArgumentException if the {@code value} parameter equals {@code null}.
   */
  public static Data newBitVector(
      final BigInteger value,
      final int size) {
    InvariantChecks.checkNotNull(value);

    final DataType dt = DataType.bitVector(size);
    final Object v = BitVector.unmodifiable(BitVector.valueOf(value, size));

    return new Data(dt, v);
  }

  /**
   * Creates a data object of the BIT_VECTOR type from a BitVector object.
   *
   * @param value A BitVector object.
   * @return A new data object.
   *
   * @throws IllegalArgumentException if the {@code value} parameter equals {@code null}.
   */
  public static Data newBitVector(final BitVector value) {
    InvariantChecks.checkNotNull(value);

    final DataType dt = DataType.bitVector(value.getBitSize());
    final Object v = BitVector.unmodifiable(value);

    return new Data(dt, v);
  }

  /**
   * Creates a data object of the BIT_VECTOR type from a string.
   *
   * @param bitVectorStr Textual representation of the bit vector.
   * @param radix Radix to be used for parsing.
   * @param size Size of the resulting bit vector in bits.
   * @return A new data object.
   *
   * @throws IllegalArgumentException if the {@code s} parameter equals {@code null}.
   */
  public static Data newBitVector(
      final String bitVectorStr,
      final int radix,
      final int size) {
    InvariantChecks.checkNotNull(bitVectorStr);

    final DataType dt = DataType.bitVector(size);
    final Object v = BitVector.unmodifiable(BitVector.valueOf(bitVectorStr, radix, size));

    return new Data(dt, v);
  }

  /**
   * Creates a data object of the BIT_VECTOR type from an integer value.
   *
   * @param value Integer value to be converted.
   * @param size The bit vector size (in bits).
   * @return A new data object.
   */
  public static Data newBitVector(final int value, final int size) {
    return newBitVector((long) value, size);
  }

  /**
   * Creates a data object of the BIT_VECTOR type from a long integer value.
   *
   * @param value Long integer value to be converted.
   * @param size The bit vector size (in bits).
   * @return A new data object.
   */
  public static Data newBitVector(final long value, final int size) {
    final DataType dt = DataType.bitVector(size);
    final Object v = BitVector.unmodifiable(BitVector.valueOf(value, size));

    return new Data(dt, v);
  }

  /**
   * Creates a data object of the MAP type from the specified {@link DataMap} object.
   *
   * @param map A {@link DataMap} object.
   * @return A new data object.
   *
   * @throws IllegalArgumentException if the {@code map} parameter equals {@code null}.
   */
  public static Data newArray(final DataMap map) {
    InvariantChecks.checkNotNull(map);
    return new Data(DataType.map(
        map.getKeyType(), map.getValueType()), map.copy());
  }

  /**
   * Constructs a data object of the specified type and initializes its value with the specified
   * value object.
   *
   * @param type The type of the data.
   * @param value An object of related type that stores the data.
   *
   * @throws IllegalArgumentException if the {@code type} parameter is {@code null}.
   */
  public Data(final DataType type, final Object value) {
    InvariantChecks.checkNotNull(type);

    if (null != value && !type.getValueClass().isAssignableFrom(value.getClass())) {
      throw new IllegalArgumentException(String.format(
          "%s is illegal value type, %s is expected.",
          value.getClass().getSimpleName(), type.getValueClass().getSimpleName())
          );
    }

    this.type = type;
    this.value = value;
    this.userData = null;
  }

  /**
   * Returns information about the type of the stored value.
   *
   * @return A {@link DataType} object.
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
   * Returns an object of given type that holds the data.
   *
   * @param clazz Class object that describes the type of the value object.
   * @param <T> Type of the value object.
   *
   * @return A type-dependent object that stores the data.
   */
  public <T> T getValue(final Class<T> clazz) {
    checkConvertibleTo(clazz);
    return clazz.cast(value);
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
  public void setUserData(final Object obj) {
    this.userData = obj;
  }

  @Override
  public int hashCode() {
    final int prime = 31;
    return prime * type.hashCode() + ((value == null) ? 0 : value.hashCode());
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

  /**
   * Checks whether the stored value has the specified type
   * (comparison is based on {@link DataTypeId}).
   *
   * @param typeId {@link DataTypeId} object the data type is to be compared to.
   * @return {@code true} if the type matches the type specified by the {@code typeId}
   *         argument or {@code false} otherwise.
   */
  public boolean isType(final DataTypeId typeId) {
    return this.type.getTypeId() == typeId;
  }

  /**
   * Checks whether the stored value has the specified type
   * (comparison is based on {@link DataType}).
   *
   * @param type {@link DataType} object the data type is to be compared to.
   * @return {@code true} if the type matches the type specified by the {@code type}
   *         argument or {@code false} otherwise.
   */
  public boolean isType(final DataType type) {
    return this.type.equals(type);
  }

  /**
   * Returns a BigInteger value stored in the data object. Applicable to data objects
   * of type {@link DataTypeId#LOGIC_INTEGER}.
   *
   * @return Stored value represented by a BigInteger.
   * @throws IllegalStateException if the stored data is not convertible to {@code BigInteger}.
   */
  public BigInteger getInteger() {
    checkConvertibleTo(BigInteger.class);
    return (BigInteger) value;
  }

  /**
   * Returns a BitVector value stored in the data object. Applicable to data objects
   * of type {@link DataTypeId#BIT_VECTOR}.
   * 
   * @return Stored value represented by a {@link BitVector}.
   * @throws IllegalStateException if the stored data is not convertible to {@link BitVector}.
   */
  public BitVector getBitVector() {
    checkConvertibleTo(BitVector.class);
    return (BitVector) value;
  }

  /**
   * Returns a boolean value stored in the data object. Applicable to data objects
   * of type {@link DataTypeId#LOGIC_BOOLEAN}.
   *
   * @return Stored value represented by a boolean.
   * @throws IllegalStateException if the stored data is not convertible to {@code Boolean}.
   */
  public boolean getBoolean() {
    checkConvertibleTo(Boolean.class);
    return (Boolean) value;
  }

  /**
   * Returns a Double value stored in the data object. Applicable to data objects
   * of type {@link DataTypeId#LOGIC_REAL}.
   * 
   * @return Stored value represented by a Double.
   * @throws IllegalStateException if the stored data is not convertible to {@code Double}.
   */
  public double getReal() {
    checkConvertibleTo(Double.class);
    return (Double) value;
  }

  /**
   * Returns a DataMap value stored in the data object. Applicable to data objects
   * of type {@link DataTypeId#MAP}.
   *
   * @return Stored value represented by a {@code DataMap}.
   * @throws IllegalStateException if the stored data is not convertible to {@link DataMap}.
   */
  public DataMap getArray() {
    checkConvertibleTo(DataMap.class);
    return (DataMap) value;
  }

  /**
   * Checks whether all {@link Data} objects in the specified array have equal values.
   *
   * @param args Array of Data objects to be checked.
   * @return {@code true} if all objects have equal values or {@code false} otherwise.
   *
   * @throws IllegalArgumentException if any of the arguments equals {@code null}.
   */
  public static boolean equalValues(final Data... args) {
    if (args.length <= 1) {
      return true;
    }

    final Data first = args[0];
    InvariantChecks.checkNotNull(first);

    for (int index = 1; index < args.length; ++index) {
      final Data current = args[index];
      InvariantChecks.checkNotNull(current);

      if (!first.equals(current)) {
        return false;
      }
    }

    return true;
  }

  /**
   * Checks whether all {@link Data} objects in the specified array have equal types.
   *
   * @param args Array of Data objects to be checked.
   * @return {@code true} if all objects have equal types or {@code false} otherwise.
   *
   * @throws IllegalArgumentException if any of the arguments equals {@code null}.
   */
  public static boolean equalTypes(final Data... args) {
    if (args.length <= 1) {
      return true;
    }

    final Data first = args[0];
    InvariantChecks.checkNotNull(first);

    final DataType type = first.getType();
    for (int index = 1; index < args.length; ++index) {
      final Data current = args[index];
      InvariantChecks.checkNotNull(current);

      if (!current.isType(type)) {
        return false;
      }
    }

    return true;
  }

  private void checkConvertibleTo(final Class<?> clazz) {
    if (!clazz.isAssignableFrom(value.getClass())) {
      throw new IllegalStateException(String.format(
          "%s data is not convertible to %s.",
          value.getClass().getSimpleName(), clazz.getSimpleName())
          );
    }
  }
}
