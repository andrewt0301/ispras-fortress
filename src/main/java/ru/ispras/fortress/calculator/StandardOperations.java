/*
 * Copyright 2015 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.calculator;

import java.util.Arrays;
import java.util.Collections;
import java.util.EnumMap;
import java.util.Map;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.DataTypeId;
import ru.ispras.fortress.data.types.bitvector.BitVector;
import ru.ispras.fortress.data.types.bitvector.BitVectorMath;
import ru.ispras.fortress.data.types.datamap.DataMap;
import ru.ispras.fortress.expression.StandardOperation;


final class StandardOperations {
  private static abstract class OpImpl implements Operation<StandardOperation> {
    private final StandardOperation id;
    private final ArityRange arity;
  
    public OpImpl(StandardOperation id, ArityRange arity) {
      this.id = id;
      this.arity = arity;
    }
  
    @Override
    public final StandardOperation getOperationId() {
      return id;
    }
  
    @Override
    public final ArityRange getOperationArity() {
      return arity;
    }
  
    @Override
    public boolean validTypes(Data... operands) {
      return OperationGroup.equalTypes(operands);
    }
  
    abstract public Data calculate(Data... operands);
  }

  public static Map<StandardOperation, Operation<StandardOperation>> arrayOps() {
    return operationSet(StandardOperation.class,
      new OpImpl(StandardOperation.SELECT, ArityRange.BINARY) {
        @Override
        public Data calculate(Data... operands) {
          final DataMap map = operands[0].getArray();
          return map.get(operands[1]);
        }

        @Override
        public boolean validTypes(Data... operands) {
          final DataType arrayType = operands[0].getType();
          return operands[0].isType(DataTypeId.MAP) &&
                 operands[1].isType((DataType) arrayType.getAttribute(DataTypeId.Attribute.KEY));
        }
      },

      new OpImpl(StandardOperation.STORE, ArityRange.TERNARY) {
        @Override
        public Data calculate(Data... operands) {
          final DataMap map = operands[0].getArray().copy();
          map.put(operands[1], operands[2]);
          return Data.newArray(map);
        }

        @Override
        public boolean validTypes(Data... operands) {
          final DataType arrayType = operands[0].getType();
          return operands[0].isType(DataTypeId.MAP) &&
                 operands[1].isType((DataType) arrayType.getAttribute(DataTypeId.Attribute.KEY)) &&
                 operands[2].isType((DataType) arrayType.getAttribute(DataTypeId.Attribute.VALUE));
        }
      });
  }

  private static class BitVectorOp extends OpImpl {
    private final BitVectorMath.Operations operation;

    public BitVectorOp(StandardOperation opId, BitVectorMath.Operations operation) {
      super(opId, translate(operation.getOperands()));
      this.operation = operation;
    }

    private static ArityRange translate(BitVectorMath.Operands arity) {
      switch (arity) {
      case UNARY: return ArityRange.UNARY;
      case BINARY: return ArityRange.BINARY;
      case TERNARY: return ArityRange.TERNARY;
      }
      throw new IllegalArgumentException();
    }

    @Override
    public Data calculate(Data... operands) {
      switch (operation.getOperands()) {
      case UNARY:
        return Data.newBitVector(operation.execute(bvarg(operands, 0)));
      case BINARY:
        return Data.newBitVector(operation.execute(bvarg(operands, 0), bvarg(operands, 1)));
      }
      throw new UnsupportedOperationException(
          "Invalid operation arity: " + operation.getOperands());
    }
  }

  private static class BitVectorCmp extends BitVectorOp {
    public BitVectorCmp(StandardOperation id, BitVectorMath.Operations operation) {
      super(id, operation);
    }

    @Override
    public Data calculate(Data... operands) {
      final BitVector bv = super.calculate(operands).getBitVector();
      return Data.newBoolean(bv.equals(BitVector.TRUE));
    }
  }

  public static Map<StandardOperation, Operation<StandardOperation>> bitVectorOps() {
    return operationSet(StandardOperation.class,
        new BitVectorOp(StandardOperation.BVAND, BitVectorMath.Operations.AND),
        new BitVectorOp(StandardOperation.BVOR, BitVectorMath.Operations.OR),
        new BitVectorOp(StandardOperation.BVXOR, BitVectorMath.Operations.XOR),
        new BitVectorOp(StandardOperation.BVNOT, BitVectorMath.Operations.NOT),
        new BitVectorOp(StandardOperation.BVNAND, BitVectorMath.Operations.NAND),
        new BitVectorOp(StandardOperation.BVNOR, BitVectorMath.Operations.NOR),
        new BitVectorOp(StandardOperation.BVXNOR, BitVectorMath.Operations.XNOR),
        new BitVectorOp(StandardOperation.BVLSHL, BitVectorMath.Operations.SHL),
        new BitVectorOp(StandardOperation.BVASHL, BitVectorMath.Operations.SHL),
        new BitVectorOp(StandardOperation.BVLSHR, BitVectorMath.Operations.LSHR),
        new BitVectorOp(StandardOperation.BVASHR, BitVectorMath.Operations.ASHR),
        new BitVectorOp(StandardOperation.BVROL, BitVectorMath.Operations.ROTL),
        new BitVectorOp(StandardOperation.BVROR, BitVectorMath.Operations.ROTR),
        new BitVectorOp(StandardOperation.BVADD, BitVectorMath.Operations.ADD),
        new BitVectorOp(StandardOperation.BVSUB, BitVectorMath.Operations.SUB),
        new BitVectorOp(StandardOperation.BVNEG, BitVectorMath.Operations.NEG),

        new BitVectorCmp(StandardOperation.BVULE, BitVectorMath.Operations.ULE),
        new BitVectorCmp(StandardOperation.BVULT, BitVectorMath.Operations.ULT),
        new BitVectorCmp(StandardOperation.BVUGE, BitVectorMath.Operations.UGE),
        new BitVectorCmp(StandardOperation.BVUGT, BitVectorMath.Operations.UGT),
        new BitVectorCmp(StandardOperation.BVSLE, BitVectorMath.Operations.SLE),
        new BitVectorCmp(StandardOperation.BVSLT, BitVectorMath.Operations.SLT),
        new BitVectorCmp(StandardOperation.BVSGE, BitVectorMath.Operations.SGE),
        new BitVectorCmp(StandardOperation.BVSGT, BitVectorMath.Operations.SGT),

        new OpImpl(StandardOperation.BVCONCAT, ArityRange.BINARY) {
          @Override
          public Data calculate(Data... operands) {
            final BitVector bv =
                BitVector.newMapping(bvarg(operands, 1), bvarg(operands, 0));
            return Data.newBitVector(bv);
          }

          @Override
          public boolean validTypes(Data... operands) {
            for (Data data : operands) {
              if (!data.isType(DataTypeId.BIT_VECTOR)) {
                return false;
              }
            }
            return true;
          }
        });
  }

  private static BitVector bvarg(Data[] operands, int i) {
    return operands[i].getBitVector();
  }

  public static Map<StandardOperation, Operation<StandardOperation>> realOps() {
    final Map<StandardOperation, Operation<StandardOperation>> operations =
      operationSet(StandardOperation.class,
        new OpImpl(StandardOperation.PLUS, ArityRange.UNARY) {
          @Override
          public Data calculate(Data... operands) {
            return operands[0];
          }
        },

        new OpImpl(StandardOperation.MINUS, ArityRange.UNARY) {
          @Override
          public Data calculate(Data... operands) {
            return Data.newReal(-operands[0].getReal());
          }
        },

        new OpImpl(StandardOperation.ADD, ArityRange.BINARY_UNBOUNDED) {
          @Override
          public Data calculate(Data... operands) {
            double result = operands[0].getReal();
            for (int index = 1; index < operands.length; ++index) {
              result += operands[index].getReal();
            }
            return Data.newReal(result);
          }
        },

        new OpImpl(StandardOperation.SUB, ArityRange.BINARY_UNBOUNDED) {
          @Override
          public Data calculate(Data... operands) {
            double result = operands[0].getReal();
            for (int index = 1; index < operands.length; ++index) {
              result -= operands[index].getReal();
            }
            return Data.newReal(result);
          }
        },

        new OpImpl(StandardOperation.MUL, ArityRange.BINARY_UNBOUNDED) {
          @Override
          public Data calculate(Data... operands) {
            double result = operands[0].getReal();
            for (int index = 1; index < operands.length; ++index) {
              result *= operands[index].getReal();
            }
            return Data.newReal(result);
          }
        },

        new OpImpl(StandardOperation.DIV, ArityRange.BINARY) {
          @Override
          public Data calculate(Data... operands) {
            final double value1 = operands[0].getReal();
            final double value2 = operands[1].getReal();

            return Data.newReal(value1 / value2);
          }
        },

        new OpImpl(StandardOperation.ABS, ArityRange.UNARY) {
          @Override
          public Data calculate(Data... operands) {
            final double value = operands[0].getReal();
            if (value < 0) {
              return Data.newReal(-value);
            }
            return operands[0];
          }
        });
      operations.putAll(ordered(Double.class));
      return operations;
  }

  public static <T extends Comparable<T>>
  Map<StandardOperation, Operation<StandardOperation>> ordered(final Class<T> c) {
    return operationSet(StandardOperation.class,
        new OpImpl(StandardOperation.GREATER, ArityRange.BINARY) {
          @Override
          public Data calculate(Data... operands) {
            return Data.newBoolean(compare(c, operands[0], operands[1]) > 0);
          }
        },

        new OpImpl(StandardOperation.GREATEREQ, ArityRange.BINARY) {
          @Override
          public Data calculate(Data... operands) {
            return Data.newBoolean(compare(c, operands[0], operands[1]) >= 0);
          }
        },

        new OpImpl(StandardOperation.LESS, ArityRange.BINARY) {
          @Override
          public Data calculate(Data... operands) {
            return Data.newBoolean(compare(c, operands[0], operands[1]) < 0);
          }
        },

        new OpImpl(StandardOperation.LESSEQ, ArityRange.BINARY) {
          @Override
          public Data calculate(Data... operands) {
            return Data.newBoolean(compare(c, operands[0], operands[1]) <= 0);
          }
        },

        new OpImpl(StandardOperation.MAX, ArityRange.UNARY_UNBOUNDED) {
          @Override
          public Data calculate(Data... operands) {
            Data value = operands[0];
            for (int i = 1; i < operands.length; ++i) {
              if (compare(c, operands[i], value) > 0) {
                value = operands[i];
              }
            }
            return value;
          }
        },

        new OpImpl(StandardOperation.MIN, ArityRange.UNARY_UNBOUNDED) {
          @Override
          public Data calculate(Data... operands) {
            Data value = operands[0];
            for (int i = 1; i < operands.length; ++i) {
              if (compare(c, operands[i], value) < 0) {
                value = operands[i];
              }
            }
            return value;
          }
        });
  }

  private static <T extends Comparable<T>>
  int compare(Class<T> c, Data lhs, Data rhs) {
    return lhs.getValue(c).compareTo(rhs.getValue(c));
  }

  private static <T extends Enum<T>>
  Map<T, Operation<T>> operationSet(Class<T> c, Operation<T>... operations) {
    final Map<T, Operation<T>> map = new EnumMap<T, Operation<T>>(c);
    for (Operation<T> op : operations) {
      map.put(op.getOperationId(), op);
    }
    return map;
  }
}
