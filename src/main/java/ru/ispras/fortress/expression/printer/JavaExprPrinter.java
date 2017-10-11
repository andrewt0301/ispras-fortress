/*
 * Copyright 2017 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.expression.printer;

import java.math.BigInteger;
import java.util.EnumMap;
import java.util.Map;

import ru.ispras.fortress.data.DataTypeId;
import ru.ispras.fortress.data.types.bitvector.BitVector;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.Nodes;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.util.InvariantChecks;

/**
 * This class implements an expression printer that produces Java code.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public final class JavaExprPrinter extends MapBasedPrinter {
  private static final Map<DataTypeId, String> FACTORY_METHODS = new EnumMap<>(DataTypeId.class);
  static {
    FACTORY_METHODS.put(DataTypeId.BIT_VECTOR,    "newBitVector");
    FACTORY_METHODS.put(DataTypeId.LOGIC_BOOLEAN, "newBoolean");
    FACTORY_METHODS.put(DataTypeId.LOGIC_INTEGER, "newInteger");
    FACTORY_METHODS.put(DataTypeId.LOGIC_REAL,    "newReal");
    FACTORY_METHODS.put(DataTypeId.LOGIC_STRING,  "newString");
    FACTORY_METHODS.put(DataTypeId.UNKNOWN,       "newUnknown");
  }

  public JavaExprPrinter() {
    setVisitor(new Visisor());
  }

  protected class Visisor extends ExprTreeVisitor {
    @Override
    public void onOperationBegin(final NodeOperation expr) {
      final Enum<?> op = expr.getOperationId();
      if (op instanceof StandardOperation) {
        appendText(Nodes.class.getSimpleName());
        appendText(".");
        appendText(expr.getOperationId().name());
        appendText("(");
      } else {
        appendText(String.format("new %s(", NodeOperation.class.getSimpleName()));
        appendText(expr.getOperationId().getClass().getSimpleName());
        appendText(".");
        appendText(expr.getOperationId().name());
      }
    }

    @Override
    public void onOperationEnd(final NodeOperation expr) {
      appendText(")");
    }

    @Override
    public int[] getOperandOrder() {
      return null;
    }

    @Override
    public void onOperandBegin(NodeOperation expr, Node operand, int index) {
      final Enum<?> op = expr.getOperationId();
      if (0 != index || !(op instanceof StandardOperation)) {
        appendText(", ");
      }
    }

    @Override
    public void onOperandEnd(NodeOperation operation, Node operand, int index) {
      // Nothing
    }

    @Override
    public void onValue(final NodeValue value) {
      appendText(NodeValue.class.getSimpleName());
      appendText(".");

      final String factoryMethod = FACTORY_METHODS.get(value.getDataTypeId());
      InvariantChecks.checkNotNull(factoryMethod);

      appendText(factoryMethod);
      appendText("(");

      if (value.isType(DataTypeId.BIT_VECTOR)) {
        appendText(bitVectorToString(value.getBitVector()));
      } else if (value.isType(DataTypeId.LOGIC_INTEGER)) {
        appendText(bigIntegerToString(value.getInteger()));
      } else if (value.isType(DataTypeId.LOGIC_STRING)) { 
        appendText("\"" + value.toString() + "\"");
      }else {
        appendText(value.toString());
      }

      appendText(")");
    }
  }

  public static String bitVectorToString(final BitVector value) {
    InvariantChecks.checkNotNull(value);

    final int bitSize = value.getBitSize();
    final String hexValue = value.toHexString();

    final StringBuilder sb = new StringBuilder();

    sb.append(BitVector.class.getSimpleName());
    sb.append(".valueOf(");

    if (value.getBitSize() <= Integer.SIZE) {
      sb.append(String.format("0x%s, %d)", hexValue, bitSize));
    } else if (bitSize <= Long.SIZE) {
      sb.append(String.format("0x%sL, %d)", hexValue, bitSize));
    } else {
      sb.append(String.format("\"%s\", 16, %d)", hexValue, bitSize));
    }

    return sb.toString();
  }

  public static String bigIntegerToString(final BigInteger value) {
    InvariantChecks.checkNotNull(value);
    return String.format("new %s(\"%d\", 10)", BigInteger.class.getSimpleName(), value);
  }
}
