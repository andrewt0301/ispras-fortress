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

import ru.ispras.fortress.util.InvariantChecks;

import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * The {@link DataType} class stores information about data types used by the solver engine.
 * It maintains a single instance for each data type (uniqueness is based on the data type
 * identifier and the data size).
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public final class DataType {
  /** Table that stores singleton instances of data types. */
  private static final Map<String, DataType> DATA_TYPES = new HashMap<>();

  private static final Object[] EMPTY_PARAMETERS_LIST = new Object[0];

  /**
   * The {@link DataType#LOGIC_TYPE_SIZE} constant specifies the size of logic data types.
   * Such types are not related with machine-dependent types and can have any size.
   * For this reason, we specify it as zero to distinguish from types that describe real data.
   */
  public static final int LOGIC_TYPE_SIZE = 0;

  /** Predefined logic integer data type. */
  public static final DataType INTEGER = newDataType(DataTypeId.LOGIC_INTEGER);

  /** Predefined logic real data type. */
  public static final DataType REAL = newDataType(DataTypeId.LOGIC_REAL);

  /** Predefined logic string data type. */
  public static final DataType STRING = newDataType(DataTypeId.LOGIC_STRING);

  /** Predefined logic boolean data type. */
  public static final DataType BOOLEAN = newDataType(DataTypeId.LOGIC_BOOLEAN);

  /** Predefined unknown data type. */
  public static final DataType UNKNOWN = newDataType(DataTypeId.UNKNOWN);

  private final DataTypeId typeId;
  private final String name;
  private final List<Object> parameters;

  /**
   * Returns a data type describing a bit vector of the specified size.
   * For bit vectors of the same size, the same instances are returned.
   *
   * @param size Bit vector size in bits.
   * @return Bit vector data type.
   */
  public static DataType bitVector(final int size) {
    InvariantChecks.checkGreaterThanZero(size);
    return newDataType(DataTypeId.BIT_VECTOR, size);
  }

  /**
   * Returns a data type describing a map that uses key and values of the specified data type.
   * For maps with matching key and value data types, the same instances are returned.
   *
   * @param keyType Key type.
   * @param valueType Value type.
   * @return Map data type.
   */
  public static DataType map(
      final DataType keyType,
      final DataType valueType) {
    InvariantChecks.checkNotNull(keyType);
    InvariantChecks.checkNotNull(valueType);

    return newDataType(DataTypeId.MAP, keyType, valueType);
  }

  /**
   * Returns a data type for the specified data type identifier and data size.
   * For the same identifier and data size, the same instances are returned.
   *
   * @param typeId Data type identifier.
   * @param size Data size in bits.
   * @return Data type object.
   */
  public static DataType newDataType(
      final DataTypeId typeId,
      final int size) {
    if (typeId == DataTypeId.BIT_VECTOR) {
      return newDataType(typeId, (Object) Integer.valueOf(size));
    }

    return newDataType(typeId);
  }

  /**
   * Returns an instance of a data type object based on its attributes. For objects of the same type
   * (type identifier and sizes are equal), the same instance is returned.
   *
   * @param typeId Type identifier.
   * @param parameters List of type parameters.
   * @return Data type object.
   */
  public static DataType newDataType(
      final DataTypeId typeId,
      final Object... parameters) {
    InvariantChecks.checkNotNull(typeId);

    final List<Object> list = Arrays.asList(parameters);
    typeId.validate(list);

    final String key = typeId.format(list);
    if (DATA_TYPES.containsKey(key)) {
      return DATA_TYPES.get(key);
    }

    final DataType dataType = new DataType(typeId, key, list);
    DATA_TYPES.put(key, dataType);

    return dataType;
  }

  /**
   * Constructs a data type object based on its attributes.
   *
   * @param typeId A type identifier.
   * @param name A type name.
   * @param parameters The list of type parameters.
   */
  private DataType(
      final DataTypeId typeId,
      final String name,
      final List<Object> parameters) {
    this.typeId = typeId;
    this.name = name;
    this.parameters = parameters;
  }

  /**
   * Returns a data type identifier.
   *
   * @return Data type identifier.
   */
  public DataTypeId getTypeId() {
    return typeId;
  }

  /**
   * Checks whether the specified data type identifier is used.
   *
   * @return {@code true} is the specified data type identifier is used or {@code false} otherwise.
   */
  public boolean isTypeId(final DataTypeId typeId) {
    return this.typeId == typeId;
  }

  /**
   * Returns the size of binary data in bits. Returns {@link DataType#LOGIC_TYPE_SIZE}
   * for logic data types.
   *
   * @return Data size in bits.
   */
  public int getSize() {
    if (typeId == DataTypeId.BIT_VECTOR) {
      return (Integer) DataTypeId.BIT_VECTOR.getAttribute(DataTypeId.Attribute.SIZE, parameters);
    }
    return LOGIC_TYPE_SIZE;
  }

  public Object[] getParameters() {
    return parameters.toArray(EMPTY_PARAMETERS_LIST);
  }

  public Object getAttribute(final DataTypeId.Attribute attr) {
    return typeId.getAttribute(attr, parameters);
  }

  /**
   * Returns a radix to be used for conversion data of this type to a string or vice versa.
   *
   * @return A radix value.
   */
  public int getTypeRadix() {
    return typeId.radix(getSize());
  }

  /**
   * Returns the class that is used to store data (internal representation).
   *
   * @return The class that is used to store data.
   */
  public Class<?> getValueClass() {
    return typeId.getValueClass();
  }

  /**
   * Creates an instance of a data object of a corresponding data type.
   *
   * @param value The text representation of a value.
   * @param radix The radix to be used for parsing.
   * @return A new data object.
   */
  public Data valueOf(final String value, final int radix) {
    InvariantChecks.checkNotNull(value);

    // Cleans extra spaces
    final String cleanValue = value.replaceAll("\\s?", "");
    return new Data(this, typeId.valueOf(cleanValue, radix, parameters));
  }

  /**
   * Creates an instance of a data type from the its textual representation.
   * If such type has already been registered the existing instance will be returned.
   *
   * @param text Textual representation of the data type.
   * @return Data type.
   */
  public static DataType typeOf(final String text) {
    InvariantChecks.checkNotNull(text);

    if (DATA_TYPES.containsKey(text)) {
      return DATA_TYPES.get(text);
    }

    DataType type;
    for (final DataTypeId tid : DataTypeId.values()) {
      if ((type = tid.typeOf(text)) != null) {
        return type;
      }
    }

    throw new IllegalArgumentException("Invalid DataType text representation: " + text);
  }

  /**
   * Creates an uninitialized data object (the value is set to null).
   *
   * @return A new data object.
   */
  public Data valueUninitialized() {
    return new Data(this, null);
  }

  @Override
  public String toString() {
    return name;
  }

  @Override
  public int hashCode() {
    return name.hashCode();
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

    final DataType other = (DataType) obj;
    if (typeId != other.typeId) {
      return false;
    }

    if (getSize() != other.getSize()) {
      return false;
    }

    return getValueClass().equals(other.getValueClass());
  }
}
