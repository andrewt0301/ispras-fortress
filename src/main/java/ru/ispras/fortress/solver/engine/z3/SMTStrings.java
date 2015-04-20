/*
 * Copyright 2013-2014 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.solver.engine.z3;

import java.math.BigInteger;
import java.util.EnumMap;
import java.util.Map;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.DataTypeId;
import ru.ispras.fortress.data.types.bitvector.BitVector;
import ru.ispras.fortress.util.InvariantChecks;

public final class SMTStrings {
  private SMTStrings() {}

  public static final String SPACE = " ";
  public static final String BRACKET_OPEN = "(";
  public static final String BRACKET_CLOSE = ")";
  public static final String HYPHEN = "-";
  public static final String UNDERLINE = "_";

  public static final String ZERO = "0";
  public static final String ONE = "1";

  public static final String EMPTY = "";
  public static final String TRUE = "true";
  public static final String FALSE = "false";
  public static final String DEFAULT_ARRAY = "DefaultArrayLiteral!%d";

  public static final String BV_BIN_PREFIX = "#b";
  public static final String BV_HEX_PREFIX = "#x";

  public static final String TYPE_BOOL = "Bool";
  public static final String TYPE_INT = "Int";
  public static final String TYPE_REAL = "Real";
  public static final String TYPE_BITVECTOR = "(_ BitVec %d)";
  public static final String TYPE_ARRAY = "(Array %s %s)";

  public static final String ASSERT = "(assert %s)%n";
  public static final String DECLARE_CONST = "(declare-const %s %s)%n";
  public static final String DEFINE_FUN = "(define-fun %s)%n";
  public static final String CHECK_SAT = "(check-sat)";
  public static final String GET_VALUE = "(get-value (%s))%n";
  public static final String GET_MODEL = "(get-model)";
  public static final String EXIT = "(exit)";

  public static final String NEGATION = "(- %s)";
  public static final String PARAM_DEF = "(%s %s)";

  private static final Map<DataTypeId, String> typeMap = createTypeMap();

  private static Map<DataTypeId, String> createTypeMap() {
    final Map<DataTypeId, String> result = new EnumMap<DataTypeId, String>(DataTypeId.class);

    result.put(DataTypeId.BIT_VECTOR, TYPE_BITVECTOR);
    result.put(DataTypeId.LOGIC_BOOLEAN, TYPE_BOOL);
    result.put(DataTypeId.LOGIC_INTEGER, TYPE_INT);
    result.put(DataTypeId.LOGIC_REAL, TYPE_REAL);
    result.put(DataTypeId.MAP, TYPE_ARRAY);

    return result;
  }

  public static String textForType(final DataType type) {
    InvariantChecks.checkNotNull(type);

    if (!typeMap.containsKey(type.getTypeId())) {
      throw new IllegalArgumentException("Unsupported type: " + type.getTypeId());
    }

    final Object[] parameters = type.getParameters();
    for (int i = 0; i < parameters.length; ++i) {
      if (parameters[i] instanceof DataType) {
        parameters[i] = textForType((DataType) parameters[i]);
      }
    }

    return String.format(typeMap.get(type.getTypeId()), parameters);
  }

  public static String textForData(final Data data) {
    InvariantChecks.checkNotNull(data);

    switch (data.getType().getTypeId()) {
      case BIT_VECTOR: {
        final BitVector value = (BitVector) data.getValue();
        return (data.getType().getTypeRadix() == 16) ?
          BV_HEX_PREFIX + value.toHexString() : BV_BIN_PREFIX + value.toBinString();
      }

      case LOGIC_BOOLEAN: {
        final Boolean value = (Boolean) data.getValue();
        return value ? TRUE : FALSE;
      }

      case LOGIC_INTEGER: {
        final BigInteger value = (BigInteger) data.getValue();
        return (value.compareTo(BigInteger.ZERO) >= 0) ?
          value.toString() : String.format(NEGATION, value.abs());
      }

      case LOGIC_REAL: {
        final double value = (Double) data.getValue();
        return (value >= 0) ? Double.toString(value) : String.format(NEGATION, Math.abs(value));
      }

      case MAP: {
        // Map<Data, Data> is assumed.
        final Map<?, ?> map = (Map<?, ?>) data.getValue();
        final StringBuilder builder = new StringBuilder();

        final String prefix = "(store ";

        builder.ensureCapacity(prefix.length() * map.size() + DEFAULT_ARRAY.length());
        for (int i = 0; i < map.size(); ++i) {
          builder.append(prefix);
        }
        builder.append(DEFAULT_ARRAY).append(SPACE);

        for (Map.Entry<?, ?> entry : map.entrySet()) {
          builder.append(textForData((Data) entry.getKey())).append(" ")
                 .append(textForData((Data) entry.getValue())).append(") ");
        }

        return builder.toString();
      }

      default: { // Unknown value type
        throw new IllegalArgumentException(
          "Unsupported data type: " + data.getType().getTypeId());
      }
    }
  }
}
