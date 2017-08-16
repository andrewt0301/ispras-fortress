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

import static ru.ispras.fortress.util.InvariantChecks.checkNotNull;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.solver.engine.smt.SmtRegExp;

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
  public DataMap(final DataType keyType, final DataType valueType) {
    this(keyType, valueType, null, new LinkedHashMap<Data, Data>());

    checkNotNull(keyType);
    checkNotNull(valueType);
  }

  private DataMap(
      final DataType keyType,
      final DataType valueType,
      final Data constant,
      final Map<Data, Data> map) {
    this.keyType = keyType;
    this.valueType = valueType;
    this.map = map;
    this.constant = constant;
  }

  public Data getConstant() {
    return this.constant;
  }

  public void setConstant(final Data data) {
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
  public boolean containsKey(final Object o) {
    return isKey(o) && map.containsKey(o);
  }

  @Override
  public boolean containsValue(final Object o) {
    return isValue(o) && map.containsValue(o) || o.equals(constant);
  }

  @Override
  public Data get(final Object o) {
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
  public Data put(final Data key, final Data value) {
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
  public Data remove(final Object o) {
    if (isKey(o)) {
      return map.remove(o);
    }
    return null;
  }

  @Override
  public void putAll(final Map<? extends Data, ? extends Data> m) {
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
  public boolean equals(final Object o) {
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

  private static boolean observeEquals(
      final Map<Data, Data> source,
      final Map<Data, Data> target) {
    for (final Map.Entry<Data, Data> entry : source.entrySet()) {
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
    for (final Map.Entry<Data, Data> entry : map.entrySet()) {
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
  public static DataMap valueOf(
      final String s, 
      final DataType keyType,
      final DataType valueType) {
    checkNotNull(s);
    checkNotNull(keyType);
    checkNotNull(valueType);

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
  private static Data readData(final String s, final DataType type) {
    final int radix;

    if (Pattern.compile(SmtRegExp.LINE_START + SmtRegExp.VALUE_BIN).matcher(s).matches()) {
      radix = 2;
    } else if (Pattern.compile(SmtRegExp.LINE_START + SmtRegExp.VALUE_HEX).matcher(s).matches()) {
      radix = 16;
    } else {
      radix = 10; // decimal value by default
    }

    return type.valueOf(s.replaceAll(SmtRegExp.VALUE_TRIM_PTRN, ""), radix);
  }

  /**
   * Create copy of this map.
   *
   * @return copy of this map
   */
  public DataMap copy() {
    return new DataMap(keyType, valueType, constant, new LinkedHashMap<>(map));
  }

  /**
   * Create unmodifiable copy of this map.
   *
   * @return unmodifiable copy of this map
   */
  public DataMap unmodifiableCopy() {
    return new DataMap(keyType,
                       valueType,
                       constant,
                       Collections.unmodifiableMap(new LinkedHashMap<>(map)));
  }

  /**
   * Check if object is {@link ru.ispras.fortress.data.Data Data} instance with
   * type conforming to key type of this map.
   */
  private boolean isKey(final Object o) {
    return getData(o).getType().equals(keyType);
  }

  /**
   * Check if object is {@link ru.ispras.fortress.data.Data Data} instance with
   * type conforming to value type of this map.
   */
  private boolean isValue(final Object o) {
    return getData(o).getType().equals(valueType);
  }

  /**
   * Cast from {@code Object} to {@code Data} instance.
   */
  private static Data getData(final Object o) {
    checkNotNull(o);
    return (Data) o;
  }
}
