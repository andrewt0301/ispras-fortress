package ru.ispras.fortress.data.types.datamap;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;

import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

public final class DataMap implements Map<Data, Data> {
  private final DataType keyType;
  private final DataType valueType;
  private final Map<Data, Data> map;

  public DataMap(DataType keyType, DataType valueType) {
    this(keyType, valueType, new LinkedHashMap<Data, Data>());

    notnull(keyType);
    notnull(valueType);
  }

  public DataMap(DataMap source) {
    this(source.keyType,
         source.valueType,
         new LinkedHashMap<>(source.map));
  }

  private DataMap(DataType keyType, DataType valueType, Map<Data, Data> map) {
    this.keyType = keyType;
    this.valueType = valueType;
    this.map = map;
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
    return isValue(o) && map.containsValue(o);
  }

  @Override
  public Data get(Object o) {
    if (isKey(o)) {
      return map.get(o);
    }
    return null;
  }

  @Override
  public Data put(Data key, Data value) {
    if (isKey(key) && isValue(value)) {
      return map.put(key, value);
    }
    if (!isKey(key)) {
      throw new IllegalArgumentException("Key type doesn't match");
    }
    throw new IllegalArgumentException("Value type doesn't match");
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
           rhs.map.equals(map);
  }

  @Override
  public int hashCode() {
    return map.hashCode();
  }

  public DataType getKeyType() {
    return keyType;
  }

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

  public static DataMap valueOf(String s, DataType keyType, DataType valueType) {
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

  private static Data readData(String s, DataType type) {
    return type.valueOf(s, type.getTypeRadix());
  }

  public DataMap unmodifiable() {
    return new DataMap(keyType,
                       valueType,
                       Collections.unmodifiableMap(new LinkedHashMap<>(map)));
  }

  private boolean isKey(Object o) {
    return getData(o).getType().equals(keyType);
  }

  private boolean isValue(Object o) {
    return getData(o).getType().equals(valueType);
  }

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
