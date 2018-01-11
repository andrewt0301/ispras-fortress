/*
 * Copyright 2012-2016 ISP RAS (http://www.ispras.ru)
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

import ru.ispras.fortress.data.types.Radix;
import ru.ispras.fortress.data.types.bitvector.BitVector;
import ru.ispras.fortress.data.types.datamap.DataMap;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * The {@link DataTypeId} enumeration is used to specify type of data a solver operates with.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public enum DataTypeId {
  /**
   * A bit vector type. Represents some data buffer of a specified size.
   */
  BIT_VECTOR(BitVector.class, false) {
    Object valueOf(final String s, final int radix, final List<Object> params) {
      final int size = (Integer) params.get(0);
      return BitVector.unmodifiable(BitVector.valueOf(s, radix, size));
    }

    int radix(final int size) {
      // TODO: see this code. It is simplified to always use BIN_RADIX. Probably, it could be done
      // better.
      return Radix.BIN.value();

      // If the size if proportional to 4, we print it as a hexadecimal value. Otherwise, as a
      // binary value.
      // return (0 == (size % BITS_IN_HEX)) ? HEX_RADIX : BIN_RADIX;
    }

    void validate(final List<Object> params) {
      report(params, Integer.class);
    }

    String format(final List<Object> params) {
      return String.format("(%s %d)", name(), params.get(0));
    }

    DataType typeOf(final String text) {
      final Matcher matcher =
        Pattern.compile(String.format("^\\(%s[ ](\\d+)\\)$", name())).matcher(text);

      if (!matcher.matches()) {
        return null;
      }

      return DataType.newDataType(this, (Object) Integer.valueOf(matcher.group(1)));
    }

    @Override
    public Object getAttribute(final Attribute a, final List<Object> params) {
      if (a == Attribute.SIZE) {
        return params.get(0);
      }

      return null;
    }
  },

  /**
   * A boolean type. It is a logic type. This means it has no connection with machine-dependent
   * types used to store boolean values (like BYTE, WORD, etc.). The size attribute is not
   * applicable.
   */
  LOGIC_BOOLEAN(Boolean.class, true) {
    Object valueOf(final String s, final int radix, final List<Object> params) {
      return Boolean.valueOf(s);
    }

    int radix(final int size) {
      return Radix.BIN.value();
    }

    void validate(final List<Object> params) {
      report(params);
    }

    String format(final List<Object> params) {
      return name();
    }

    DataType typeOf(final String text) {
      if (!text.equals(name())) {
        return null;
      }

      return DataType.BOOLEAN;
    }
  },

  /**
   * An integer type. It is a logic type. This means that it has no connection with
   * machine-dependent types used to store integer values (like 16-bit, 32-bit or 64-bit integer
   * representations). The size attribute is not applicable.
   */
  LOGIC_INTEGER(BigInteger.class, true) {
    Object valueOf(final String s, final int radix, final List<Object> params) {
      return new BigInteger(s, radix);
    }

    int radix(final int size) {
      return Radix.DEC.value();
    }

    void validate(final List<Object> params) {
      report(params);
    }

    String format(final List<Object> params) {
      return name();
    }

    DataType typeOf(final String text) {
      if (!text.equals(name())) {
        return null;
      }

      return DataType.INTEGER;
    }
  },

  /**
   * A real type. It is a logic type. This means that it has no connection with machine-dependent
   * types used store to floating point numbers. The size attribute is not applicable.
   */
  LOGIC_REAL(Double.class, true) {
    Object valueOf(final String s, final int radix, final List<Object> params) {
      return Double.valueOf(s);
    }

    int radix(final int size) {
      return Radix.DEC.value();
    }

    void validate(final List<Object> params) {
      report(params);
    }

    String format(final List<Object> params) {
      return name();
    }

    DataType typeOf(final String text) {
      if (!text.equals(name())) {
        return null;
      }

      return DataType.REAL;
    }
  },

  /**
   * A string  type. It is a logic type. This means that it has no connection with
   * machine-dependent types. The size attribute is not applicable.
   */
  LOGIC_STRING(String.class, true) {
    Object valueOf(final String s, final int radix, final List<Object> params) {
      return s;
    }

    int radix(final int size) { return 0; }
    void validate(final List<Object> params) {}
    String format(final List<Object> params) { return name(); }

    DataType typeOf(final String text) {
      if (!text.equals(name())) {
        return null;
      }

      return DataType.STRING;
    }
  },

  /**
   * A mapping type. Represents mappings from values of one type to another.
   */

  MAP(DataMap.class, true) {
    Object valueOf(final String s, final int radix, final List<Object> params) {
      final DataType keyType = (DataType) params.get(0);
      final DataType valueType = (DataType) params.get(1);
      return DataMap.valueOf(s, keyType, valueType);
    }

    /** 
     * {@inheritDoc} Radix for composite types like MAP is undefined.
     */
    int radix(final int size) {
      return 0;
    }

    void validate(final List<Object> params) {
      report(params, DataType.class, DataType.class);
    }

    String format(final List<Object> params) {
      return String.format("(%s %s %s)", name(), params.get(0), params.get(1));
    }

    DataType typeOf(final String text) {
      final Matcher matcher =
        Pattern.compile(String.format("^\\(%s[ ](.+)[ ](.+)\\)$", name())).matcher(text);

      if (!matcher.matches()) {
        return null;
      }

      String keyTypeText = matcher.group(1);
      String valueTypeText = matcher.group(2);

      if (valueTypeText.charAt(valueTypeText.length() - 1) == ')') {
        int depth = 0;
        for (int i = 0; i < keyTypeText.length(); ++i) {
          final char c = keyTypeText.charAt(i);
          if (c == '(') {
            ++depth;
          } else if (c == ')') {
            --depth;
          } else if (c == ' ' && depth == 0) {
            valueTypeText = keyTypeText.substring(i + 1) + " " + valueTypeText;
            keyTypeText = keyTypeText.substring(0, i);
            break;
          }
        }
      }

      final Object keyType = DataType.typeOf(keyTypeText);
      final Object valueType = DataType.typeOf(valueTypeText);

      return DataType.newDataType(this, keyType, valueType);
    }

    @Override
    public Object getAttribute(final Attribute a, final List<Object> params) {
      if (a == Attribute.KEY) {
        return params.get(0);
      }

      else if (a == Attribute.VALUE) {
        return params.get(1);
      }

      return null;
    }
  },

  /**
   * Uninterpreted data, that should not be passed to solver.
   */
  UNKNOWN(Object.class, true) {
    Object valueOf(final String s, final int radix, final List<Object> params) {
      throw new UnsupportedOperationException("Unable to create a value of an unknown type.");
    }

    int radix(final int size) {
      return 0;
    }

    void validate(final List<Object> params) {}

    String format(final List<Object> params) {
      return name();
    }

    DataType typeOf(final String text) {
      if (!text.equals(name())) {
        return null;
      }

      return DataType.UNKNOWN;
    }
  };

  private final Class<?> valueClass;
  private final boolean isLogic; 

  /**
   * Creates a description of a data type.
   * 
   * @param valueClass The type of the object used to store the data (internal representation).
   * @param isLogic Specifies whether the type is logical which means that it is purely
   * mathematical and is not associated with data types implemented in real hardware.
   */
  private DataTypeId(final Class<?> valueClass, final boolean isLogic) {
    this.valueClass = valueClass;
    this.isLogic = isLogic;
  }

  /**
   * Returns information on the type used to store the data (internal representation).
   * 
   * @return Value type.
   */
  Class<?> getValueClass() {
    return valueClass;
  }

  /**
   * Checks whether the specified type is logical which means that it is purely
   * mathematical and is not associated with data types implemented in real hardware.
   * 
   * @return {@code true} if the type is logic or {@code false} otherwise.
   */

  public boolean isLogic() {
    return isLogic;
  }

  /**
   * Creates a value of the given type (described by the valueClass type) basing on its textual
   * representation.
   * 
   * @param s Textual representation of the value.
   * @param radix Radix to be used for conversion.
   * @param size Data size in bits.
   * @return Value of the given type packed into an Object value.
   */
  Object valueOf(final String s, final int radix, final int size) {
    final List<Object> list = new ArrayList<Object>();
    list.add(size);
    return valueOf(s, radix, list);
  }

  public static enum Attribute {
    SIZE, KEY, VALUE
  }

  abstract Object valueOf(String s, int radix, List<Object> params);

  /**
   * Returns radix to be used to convert data of this type to a string or vice versa.
   * 
   * @param size Data size in bits (needed where applicable).
   * @return Radix value.
   */

  abstract int radix(int size);

  abstract String format(List<Object> params);

  abstract void validate(List<Object> params);

  abstract DataType typeOf(String text);

  private static void report(final List<Object> passed, final Class<?>... required) {
    if (passed.size() != required.length) {
      throw new IllegalArgumentException(String.format(
        "Invalid number of type parameters: %d, expected: %d.", passed.size(), required.length));
    }

    for (int i = 0; i < passed.size(); ++i) {
      if (passed.get(i).getClass() != required[i]) {
        throw new IllegalArgumentException(String.format(
          "Invalid parameter type: %s, expected: %s.", passed.get(i).getClass().getName(),
          required[i].getName()));
      }
    }
  }

  public Object getAttribute(final Attribute a, final List<Object> params) {
    return null;
  }
}
