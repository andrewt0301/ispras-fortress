/*
 * Copyright 2014 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.data.types.datamap;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.solver.engine.z3.SMTRegExp;

import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.regex.Pattern;

/**
 * The DataMap class represents mappings using Fortress data types with
 * runtime type checking.
 */

public final class DataMap implements Map<Data, Data> {
  private final DataType keyType;
  private final DataType valueType;
  private final Map<Data, Data> map;
  private Data constant;

  /**
   * Create map for given key type and value type.
   *
   * @param keyType {@link ru.ispras.fortress.data.DataType DataType} instance for keys
   * @param valueType {@link ru.ispras.fortress.data.DataType DataType} instance for values
   */

  public DataMap(DataType keyType, DataType valueType) {
    this(keyType, valueType, null, new LinkedHashMap<Data, Data>());

    notnull(keyType);
    notnull(valueType);
  }

  private DataMap(DataType keyType, DataType valueType, Data constant, Map<Data, Data> map) {
    this.keyType = keyType;
    this.valueType = valueType;
    this.map = map;
    this.constant = constant;
  }

  public Data getConstant() {
    return this.constant;
  }

  public void setConstant(Data data) {
    this.constant = data;
  }

  @Override
  public int size() {
    return map.size();
  }

  @Override
  public boolean isEmpty() {
    return map.isEmpty();
  }

  @Override
  public boolean containsKey(Object o) {
    return isKey(o) && map.containsKey(o);
  }

  @Override
  public boolean containsValue(Object o) {
    return isValue(o) && map.containsValue(o) || o.equals(constant);
  }

  @Override
  public Data get(Object o) {
    if (isKey(o)) {
      final Data data = map.get(o);
      if (data == null) {
        return constant;
      }
      return data;
    }
    throw new IllegalArgumentException("Invalid key type, expected " + keyType);
  }

  @Override
  public Data put(Data key, Data value) {
    if (isKey(key) && isValue(value)) {
      return map.put(key, value);
    }
    final String fmt = "Invalid %s type: expected %s, got %s";
    if (!isKey(key)) {
      throw new IllegalArgumentException(String.format(fmt, "key", keyType, key.getType()));
    }
    throw new IllegalArgumentException(String.format(fmt, "value", valueType, value.getType()));
  }

  @Override
  public Data remove(Object o) {
    if (isKey(o)) {
      return map.remove(o);
    }
    return null;
  }

  @Override
  public void putAll(Map<? extends Data, ? extends Data> m) {
    throw new UnsupportedOperationException("DataMap doesn't support putAll() method");
  }

  @Override
  public void clear() {
    map.clear();
  }

  @Override
  public Set<Data> keySet() {
    return Collections.unmodifiableSet(map.keySet());
  }

  @Override
  public Collection<Data> values() {
    return Collections.unmodifiableCollection(map.values());
  }

  @Override
  public Set<Map.Entry<Data, Data>> entrySet() {
    return Collections.unmodifiableSet(map.entrySet());
  }

  @Override
  public boolean equals(Object o) {
    if (o == null) {
      return false;
    }
    if (o == this) {
      return false;
    }
    if (o.getClass() != this.getClass()) {
      return false;
    }
    final DataMap rhs = (DataMap) o;

    return rhs.keyType.equals(keyType) &&
           rhs.valueType.equals(valueType) &&
           observeEquals(this, rhs) &&
           observeEquals(rhs, this);
  }

  private static boolean observeEquals(Map<Data, Data> source, Map<Data, Data> target) {
    for (Map.Entry<Data, Data> entry : source.entrySet()) {
      if (!entry.getValue().equals(target.get(entry.getKey()))) {
        return false;
      }
    }
    return true;
  }

  @Override
  public int hashCode() {
    return map.hashCode();
  }

  /**
   * Return type of keys in this map.
   *
   * @return type of keys in this map
   */

  public DataType getKeyType() {
    return keyType;
  }

  /**
   * Return type of values in this map.
   *
   * @return type of values in this map
   */

  public DataType getValueType() {
    return valueType;
  }

  @Override
  public String toString() {
    final StringBuilder builder = new StringBuilder();
    builder.append('(');
    for (Map.Entry<Data, Data> entry : map.entrySet()) {
      builder.append(String.format("(%s:%s)",
                                   entry.getKey().getValue(),
                                   entry.getValue().getValue()));
    }
    builder.append(')');
    return builder.toString();
  }

  /**
   * Read {@link DataMap} from string using type hints.
   *
   * @param s string representation of {@link DataMap} instance
   * @param keyType expected data type for keys in map
   * @param valueType expected data type for values in map
   * @return {@link DataMap} instance for given string representation
   *
   * @throws IllegalArgumentException if {@code s} is not valid string representation
   */

  public static DataMap valueOf(String s, DataType keyType, DataType valueType) {
    notnull(s);
    notnull(keyType);
    notnull(valueType);

    final char LPAREN = '(';
    final char RPAREN = ')';
    final char DELIM = ':';

    int depth = -1;
    int start = -1, end = -1;

    final DataMap map = new DataMap(keyType, valueType);
    for (int i = 0; i < s.length(); ++i) {
      final char c = s.charAt(i);
      if (c == LPAREN && ++depth == 1) {
        start = i + 1;
      } else if (c == RPAREN && --depth == 0) {
        map.map.put(readData(s.substring(start, end), keyType),
                    readData(s.substring(end + 1, i), valueType));
      } else if (c == DELIM && depth == 1) {
        end = i;
      }
    }
    if (depth != -1) {
      throw new IllegalArgumentException("Broken string value");
    }
    return map;
  }

  /**
   * Read {@link ru.ispras.fortress.data.Data Data} instance from string
   * using data type hint.
   *
   * @param s string representation of {@code Data} instance
   * @param type expected data type of value being read
   * @return {@link ru.ispras.fortress.data.Data Data} instance for given string representation
   */

  private static Data readData(String s, DataType type) {
    final int radix;

    if (Pattern.compile(SMTRegExp.LINE_START + SMTRegExp.VALUE_BIN).matcher(s).matches()) {
      radix = 2;
    } else if (Pattern.compile(SMTRegExp.LINE_START + SMTRegExp.VALUE_HEX).matcher(s).matches()) {
      radix = 16;
    } else {
      radix = 10; // decimal value by default
    }

    return type.valueOf(s.replaceAll(SMTRegExp.VALUE_TRIM_PTRN, ""), radix);
  }

  /**
   * Create copy of this map.
   *
   * @return copy of this map
   */

  public final DataMap copy() {
    return new DataMap(keyType, valueType, constant, new LinkedHashMap<>(map));
  }

  /**
   * Create unmodifiable copy of this map.
   *
   * @return unmodifiable copy of this map
   */

  public final DataMap unmodifiableCopy() {
    return new DataMap(keyType,
                       valueType,
                       constant,
                       Collections.unmodifiableMap(new LinkedHashMap<>(map)));
  }

  /**
   * Check if object is {@link ru.ispras.fortress.data.Data Data} instance with
   * type conforming to key type of this map.
   */

  private boolean isKey(Object o) {
    return getData(o).getType().equals(keyType);
  }

  /**
   * Check if object is {@link ru.ispras.fortress.data.Data Data} instance with
   * type conforming to value type of this map.
   */

  private boolean isValue(Object o) {
    return getData(o).getType().equals(valueType);
  }

  /**
   * Cast from {@code Object} to {@code Data} instance.
   */

  private static Data getData(Object o) {
    notnull(o);
    return (Data) o;
  }

  private static void notnull(Object o) {
    if (o == null) {
      throw new NullPointerException();
    }
  }
}
