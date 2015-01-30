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
import static ru.ispras.fortress.util.InvariantChecks.checkGreaterThanZero;

import java.util.List;
import java.util.Arrays;
import java.util.HashMap;

/**
 * The DataType class stores information about data types used by the solver engine. It maintains a
 * single instance for each data type (uniqueness is based on the data type identifier and the data
 * size).
 * 
 * @author Andrei Tatarnikov
 */

public final class DataType {
  /**
   * Table that stores singleton instances of data types.
   */

  private static HashMap<String, DataType> dataTypes = new HashMap<String, DataType>();
  private static Object[] EMPTY_PARAMETERS_LIST = new Object[0];

  /**
   * The LOGIC_TYPE_SIZE constant specifies the size of logic data types. Such types are not related
   * with machine-dependent types and can have any size. For this reason, we specify it as zero to
   * distinguish from types that describe real data.
   */

  public static final int LOGIC_TYPE_SIZE = 0;

  /** Predefined logic integer type. */
  public static final DataType INTEGER = newDataType(DataTypeId.LOGIC_INTEGER);

  /** Predefined logic real type. */
  public static final DataType REAL = newDataType(DataTypeId.LOGIC_REAL);

  /** Predefined logic boolean type. */
  public static final DataType BOOLEAN = newDataType(DataTypeId.LOGIC_BOOLEAN);

  /** Predefined unknown type. */
  public static final DataType UNKNOWN = newDataType(DataTypeId.UNKNOWN);

  /**
   * Returns a type describing a bit vector of the specified size.
   * 
   * @param size Bit vector size in bits
   * @return Bit vector type
   */

  public static DataType BIT_VECTOR(int size) {
    checkGreaterThanZero(size);
    return newDataType(DataTypeId.BIT_VECTOR, size);
  }

  public static DataType MAP(DataType keyType, DataType valueType) {
    checkNotNull(keyType);
    checkNotNull(valueType);

    return newDataType(DataTypeId.MAP, keyType, valueType);
  }

  public static DataType newDataType(DataTypeId typeId, int size) {
    if (typeId == DataTypeId.BIT_VECTOR) {
      return newDataType(typeId, (Object) Integer.valueOf(size));
    }

    return newDataType(typeId);
  }

  /**
   * Returns an instance of a data type object based on its attributes. For objects of the same type
   * (type identifier and sizes are equal), the same instance is returned.
   * 
   * @param typeId A type identifier
   * @param parameters The list of type parameters
   * @return A data type object
   */

  public static DataType newDataType(DataTypeId typeId, Object... parameters) {
    checkNotNull(typeId);

    final List<Object> list = Arrays.asList(parameters);
    typeId.validate(list);

    final String key = typeId.format(list);
    if (dataTypes.containsKey(key)) {
      return dataTypes.get(key);
    }

    final DataType dataType = new DataType(typeId, key, list);
    dataTypes.put(key, dataType);

    return dataType;
  }

  private final DataTypeId typeId;
  private final String name;
  private final List<Object> parameters;

  /**
   * Constructs a data type object based on its attributes.
   * 
   * @param typeId A type identifier.
   * @param size The size of data in bits.
   */

  private DataType(DataTypeId typeId, String name, List<Object> parameters) {
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
   * Returns the size of binary data in bits. Returns LOGIC_TYPE_SIZE for logic types.
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

  public Data valueOf(String value, int radix) {
    checkNotNull(value);

    value = value.replaceAll("\\s?", ""); // Removes extra spaces
    return new Data(this, typeId.valueOf(value, radix, parameters));
  }

  public static DataType typeOf(String value) {
    checkNotNull(value);

    if (dataTypes.containsKey(value)) {
      return dataTypes.get(value);
    }

    DataType type;
    for (DataTypeId tid : DataTypeId.values()) {
      if ((type = tid.typeOf(value)) != null) {
        return type;
      }
    }

    throw new IllegalArgumentException("Invalid DataType text representation: " + value);
  }

  /**
   * Creates an uninitialized data object (the value is set to null).
   * 
   * @return A new data object.
   */

  public Data valueUninitialized() {
    return new Data(this, null);
  }

  /**
   * {@inheritDoc}
   */

  @Override
  public String toString() {
    return name;
  }

  /**
   * {@inheritDoc}
   */

  @Override
  public int hashCode() {
    return name.hashCode();
  }

  /**
   * {@inheritDoc}
   */

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
