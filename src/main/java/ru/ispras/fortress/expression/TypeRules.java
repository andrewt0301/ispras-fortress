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
    public DataType getResultType(DataType[] operandTypes, int[] params) {
      return DataType.UNKNOWN;
    }
  },

  BOOLEAN {
    @Override
    public DataType getResultType(DataType[] operandTypes, int[] params) {
      return DataType.BOOLEAN;
    }
  },

  BIT_BOOLEAN {
    @Override
    public DataType getResultType(DataType[] operandTypes, int[] params) {
      return DataType.BIT_VECTOR(1);
    }
  },

  FIRST_KNOWN_BV_ARG {
    @Override
    public DataType getResultType(DataType[] operandTypes, int[] params) {
      DataType result = DataType.UNKNOWN;

      for (DataType dataType : operandTypes) {
        if (dataType.getTypeId() == DataTypeId.BIT_VECTOR) {
          result = dataType;
          break;
        }
      }

      return result;
    }
  },

  SECOND_VB_ARG {
    @Override
    public DataType getResultType(DataType[] operandTypes, int[] params) {
      if (operandTypes.length > 1 && operandTypes[1].getTypeId() == DataTypeId.BIT_VECTOR) {
        return operandTypes[1];
      }

      return DataType.UNKNOWN;
    }
  },

  FIRST_NUM_ARG {
    @Override
    public DataType getResultType(DataType[] operandTypes, int[] params) {
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
    public DataType getResultType(DataType[] operandTypes, int[] params) {
      DataType result = DataType.UNKNOWN;

      for (DataType dataType : operandTypes) {
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
    public DataType getResultType(DataType[] operandTypes, int[] params) {
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
    public DataType getResultType(DataType[] operandTypes, int[] params) {
      if (operandTypes.length != 3 && params.length != 2) {
        return DataType.UNKNOWN;
      }

      final DataType sourceType = operandTypes[2];
      if (DataTypeId.BIT_VECTOR != sourceType.getTypeId()) {
        return DataType.UNKNOWN;
      }

      final int m = sourceType.getSize();
      final int i = params[0];      
      final int j = params[1];

      if (!((m > i) && (i >= j) && (j >= 0))) {
        return DataType.UNKNOWN;
      }

      final int n = i - j + 1;
      return DataType.BIT_VECTOR(n);
    }
  },
  
  
  BVCONCAT {
    @Override
    public DataType getResultType(DataType[] operandTypes, int[] params) {
      int totalSize = 0;
      for (DataType operandType : operandTypes) {
        if (DataTypeId.BIT_VECTOR != operandType.getTypeId()) {
          return DataType.UNKNOWN;
        }
        totalSize += operandType.getSize();
      }

      return DataType.BIT_VECTOR(totalSize);
    }
  }
}
