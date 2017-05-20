/*
 * Copyright 2014-2015 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.expression;

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.DataTypeId;

enum TypeRules implements TypeRule {
  UNKNOWN {
    @Override
    public DataType getResultType(final DataType[] operandTypes, final int[] params) {
      return DataType.UNKNOWN;
    }
  },

  BOOLEAN {
    @Override
    public DataType getResultType(final DataType[] operandTypes, final int[] params) {
      return DataType.BOOLEAN;
    }
  },

  BIT_BOOLEAN {
    @Override
    public DataType getResultType(final DataType[] operandTypes, final int[] params) {
      return DataType.BIT_VECTOR(1);
    }
  },

  INTEGER {
    @Override
    public DataType getResultType(final DataType[] operandTypes, final int[] params) {
      return DataType.INTEGER;
    }
  },

  FIRST_KNOWN_BV_ARG {
    @Override
    public DataType getResultType(final DataType[] operandTypes, final int[] params) {
      DataType result = DataType.UNKNOWN;

      for (final DataType dataType : operandTypes) {
        if (dataType.getTypeId() == DataTypeId.BIT_VECTOR) {
          result = dataType;
          break;
        }
      }

      return result;
    }
  },

  SECOND_BV_ARG {
    @Override
    public DataType getResultType(final DataType[] operandTypes, final int[] params) {
      if (operandTypes.length > 1 && operandTypes[1].getTypeId() == DataTypeId.BIT_VECTOR) {
        return operandTypes[1];
      }

      return DataType.UNKNOWN;
    }
  },

  FIRST_NUM_ARG {
    @Override
    public DataType getResultType(final DataType[] operandTypes, final int[] params) {
      if (operandTypes.length > 0) {
        if (operandTypes[0].getTypeId() == DataTypeId.LOGIC_INTEGER ||
            operandTypes[0].getTypeId() == DataTypeId.LOGIC_REAL) {
          return operandTypes[0];
        }
      }

      return DataType.UNKNOWN;
    }
  },

  FIRST_KNOWN_NUM_ARG {
    @Override
    public DataType getResultType(final DataType[] operandTypes, final int[] params) {
      DataType result = DataType.UNKNOWN;

      for (final DataType dataType : operandTypes) {
        if (dataType.getTypeId() == DataTypeId.LOGIC_INTEGER ||
            dataType.getTypeId() == DataTypeId.LOGIC_REAL) {
          result = dataType;
          break;
        }
      }

      return result;
    }
  },

  ITE {
    @Override
    public DataType getResultType(final DataType[] operandTypes, final int[] params) {
      if (operandTypes.length > 2) {
        if (operandTypes[1].getTypeId() != DataTypeId.UNKNOWN) {
          return operandTypes[1];
        }

        if (operandTypes[2].getTypeId() != DataTypeId.UNKNOWN) {
          return operandTypes[2];
        }
      }

      return DataType.UNKNOWN;
    }
  },

  /**
   * Semantics of the BVEXTRACT operation as described in the SMT-LIB bit vector theory:
   * <p>
   * {@code ((_ extract i j) (_ BitVec m) (_ BitVec n))}
   * <p>
   * where
   * <ul>
   * <li>i,j,m,n are numerals
   * <li>m > i >= j >= 0,
   * <li>n = i-j+1
   * </ul>
   */

  BVEXTRACT {
    @Override
    public DataType getResultType(final DataType[] operandTypes, final int[] params) {
      if (operandTypes.length != 3 && params.length != 2) {
        return DataType.UNKNOWN;
      }

      final DataType sourceType = operandTypes[2];
      if (DataTypeId.BIT_VECTOR != sourceType.getTypeId()) {
        return DataType.UNKNOWN;
      }

      final int m = sourceType.getSize();
      final int i = Math.max(params[0], params[1]);
      final int j = Math.min(params[0], params[1]);

      if (!((m > i) && (i >= j) && (j >= 0))) {
        return DataType.UNKNOWN;
      }

      final int n = i - j + 1;
      return DataType.BIT_VECTOR(n);
    }
  },

  BVCONCAT {
    @Override
    public DataType getResultType(final DataType[] operandTypes, final int[] params) {
      int totalSize = 0;
      for (final DataType operandType : operandTypes) {
        if (DataTypeId.BIT_VECTOR != operandType.getTypeId()) {
          return DataType.UNKNOWN;
        }
        totalSize += operandType.getSize();
      }

      return DataType.BIT_VECTOR(totalSize);
    }
  },

  BVREPEAT {
    @Override
    public DataType getResultType(final DataType[] operandTypes, final int[] params) {
      return DataType.BIT_VECTOR(operandTypes[1].getSize() * params[0]);
    }
  },

  BVEXTEND {
    public DataType getResultType(final DataType[] operandTypes, final int[] params) {
      return DataType.BIT_VECTOR(operandTypes[1].getSize() + params[0]);
    }
  },

  SELECT {
    @Override
    public DataType getResultType(final DataType[] operandTypes, final int[] params) {
      return (DataType) operandTypes[0].getAttribute(DataTypeId.Attribute.VALUE);
    }
  },

  STORE {
    @Override
    public DataType getResultType(final DataType[] operandTypes, final int[] params) {
      return operandTypes[0];
    }
  }
}
