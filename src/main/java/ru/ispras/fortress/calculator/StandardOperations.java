/*
 * Copyright 2015-2018 ISP RAS (http://www.ispras.ru)
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

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.DataTypeId;
import ru.ispras.fortress.data.types.bitvector.BitVector;
import ru.ispras.fortress.data.types.bitvector.BitVectorMath;
import ru.ispras.fortress.data.types.datamap.DataMap;
import ru.ispras.fortress.expression.StandardOperation;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

final class StandardOperations {
  private StandardOperations() {}

  private abstract static class StdOperation extends CalculatorOperation<StandardOperation> {
    public StdOperation(final StandardOperation id, final ArityRange arity) {
      super(id, arity);
    }

    public abstract Data calculate(Data... operands);
  }

  public static Map<StandardOperation, Operation<StandardOperation>> arrayOps() {
    final List<StdOperation> operations = Arrays.asList(
        new StdOperation(StandardOperation.SELECT, ArityRange.BINARY) {
          @Override
          public Data calculate(final Data... operands) {
            final DataMap map = operands[0].getArray();
            return map.get(operands[1]);
          }

          @Override
          public boolean validTypes(final Data... operands) {
            final DataType arrayType = operands[0].getType();
            return operands[0].isType(DataTypeId.MAP)
                  && operands[1].isType(
                      (DataType) arrayType.getAttribute(DataTypeId.Attribute.KEY));
          }
      },

      new StdOperation(StandardOperation.STORE, ArityRange.TERNARY) {
        @Override
        public Data calculate(final Data... operands) {
          final DataMap map = operands[0].getArray().copy();
          map.put(operands[1], operands[2]);
          return Data.newArray(map);
        }

        @Override
        public boolean validTypes(final Data... operands) {
          final DataType arrayType = operands[0].getType();
          return operands[0].isType(DataTypeId.MAP)
              && operands[1].isType((DataType) arrayType.getAttribute(DataTypeId.Attribute.KEY))
              && operands[2].isType((DataType) arrayType.getAttribute(DataTypeId.Attribute.VALUE));
        }
      });

    return OperationGroup.operationMap(StandardOperation.class, operations);
  }

  private static class BitVectorOp extends StdOperation {
    private final BitVectorMath.Operations operation;

    public BitVectorOp(
        final StandardOperation opId,
        final BitVectorMath.Operations operation) {
      super(opId, translate(operation.getOperands()));
      this.operation = operation;
    }

    private static ArityRange translate(final BitVectorMath.Operands arity) {
      switch (arity) {
        case UNARY: return ArityRange.UNARY;
        case BINARY: return ArityRange.BINARY;
        case TERNARY: return ArityRange.TERNARY;
        default: throw new IllegalArgumentException();
      }
    }

    @Override
    public Data calculate(final Data... operands) {
      switch (operation.getOperands()) {
        case UNARY:
          return Data.newBitVector(operation.execute(bvarg(operands, 0)));
        case BINARY:
          return Data.newBitVector(operation.execute(bvarg(operands, 0), bvarg(operands, 1)));
        default:
          throw new UnsupportedOperationException(
              "Invalid operation arity: " + operation.getOperands());
      }
    }
  }

  private static class BitVectorCmp extends BitVectorOp {
    public BitVectorCmp(final StandardOperation id, final BitVectorMath.Operations operation) {
      super(id, operation);
    }

    @Override
    public Data calculate(final Data... operands) {
      final BitVector bv = super.calculate(operands).getBitVector();
      return Data.newBoolean(bv.equals(BitVector.TRUE));
    }
  }

  public static Map<StandardOperation, Operation<StandardOperation>> bitVectorOps() {
    final List<StdOperation> operations = Arrays.asList(
        new BitVectorOp(StandardOperation.BVAND, BitVectorMath.Operations.AND),
        new BitVectorOp(StandardOperation.BVOR, BitVectorMath.Operations.OR),
        new BitVectorOp(StandardOperation.BVXOR, BitVectorMath.Operations.XOR),
        new BitVectorOp(StandardOperation.BVNOT, BitVectorMath.Operations.NOT),
        new BitVectorOp(StandardOperation.BVNAND, BitVectorMath.Operations.NAND),
        new BitVectorOp(StandardOperation.BVNOR, BitVectorMath.Operations.NOR),
        new BitVectorOp(StandardOperation.BVXNOR, BitVectorMath.Operations.XNOR),
        new BitVectorOp(StandardOperation.BVLSHL, BitVectorMath.Operations.USHL),
        new BitVectorOp(StandardOperation.BVASHL, BitVectorMath.Operations.USHL),
        new BitVectorOp(StandardOperation.BVLSHR, BitVectorMath.Operations.LSHR),
        new BitVectorOp(StandardOperation.BVASHR, BitVectorMath.Operations.ASHR),
        new BitVectorOp(StandardOperation.BVROL, BitVectorMath.Operations.ROTL),
        new BitVectorOp(StandardOperation.BVROR, BitVectorMath.Operations.ROTR),
        new BitVectorOp(StandardOperation.BVADD, BitVectorMath.Operations.ADD),
        new BitVectorOp(StandardOperation.BVSUB, BitVectorMath.Operations.SUB),
        new BitVectorOp(StandardOperation.BVNEG, BitVectorMath.Operations.NEG),
        new BitVectorOp(StandardOperation.BVMUL, BitVectorMath.Operations.MUL),
        new BitVectorOp(StandardOperation.BVUDIV, BitVectorMath.Operations.UDIV),
        new BitVectorOp(StandardOperation.BVSDIV, BitVectorMath.Operations.SDIV),
        new BitVectorOp(StandardOperation.BVUREM, BitVectorMath.Operations.UREM),
        new BitVectorOp(StandardOperation.BVSREM, BitVectorMath.Operations.SREM),
        new BitVectorOp(StandardOperation.BVSMOD, BitVectorMath.Operations.SMOD),
        new BitVectorOp(StandardOperation.BVANDR, BitVectorMath.Operations.ANDR),
        new BitVectorOp(StandardOperation.BVNANDR, BitVectorMath.Operations.NANDR),
        new BitVectorOp(StandardOperation.BVORR, BitVectorMath.Operations.ORR),
        new BitVectorOp(StandardOperation.BVNORR, BitVectorMath.Operations.NORR),
        new BitVectorOp(StandardOperation.BVXORR, BitVectorMath.Operations.XORR),
        new BitVectorOp(StandardOperation.BVXNORR, BitVectorMath.Operations.XNORR),

        new BitVectorCmp(StandardOperation.BVULE, BitVectorMath.Operations.ULE),
        new BitVectorCmp(StandardOperation.BVULT, BitVectorMath.Operations.ULT),
        new BitVectorCmp(StandardOperation.BVUGE, BitVectorMath.Operations.UGE),
        new BitVectorCmp(StandardOperation.BVUGT, BitVectorMath.Operations.UGT),
        new BitVectorCmp(StandardOperation.BVSLE, BitVectorMath.Operations.SLE),
        new BitVectorCmp(StandardOperation.BVSLT, BitVectorMath.Operations.SLT),
        new BitVectorCmp(StandardOperation.BVSGE, BitVectorMath.Operations.SGE),
        new BitVectorCmp(StandardOperation.BVSGT, BitVectorMath.Operations.SGT),

        new StdOperation(StandardOperation.BVCONCAT, ArityRange.BINARY_UNBOUNDED) {
          // NOTE: expected operand order is from HIGH to LOW.
          @Override
          public Data calculate(final Data... operands) {
            final BitVector[] input = new BitVector[operands.length];
            for (int i = 0; i < operands.length; ++i) {
              input[i] = bvarg(operands, i);
            }
            return Data.newBitVector(BitVector.newMapping(input));
          }

          @Override
          public boolean validTypes(final Data... operands) {
            for (final Data data : operands) {
              if (!data.isType(DataTypeId.BIT_VECTOR)) {
                return false;
              }
            }
            return true;
          }
        },

        new StdOperation(StandardOperation.BV2INT, ArityRange.UNARY) {
          @Override
          public Data calculate(Data... operands) {
            return Data.newInteger(operands[0].getBitVector().intValue());
          }

          @Override
          public boolean validTypes(final Data... operands) {
            return operands[0].isType(DataTypeId.BIT_VECTOR);
          }
        },

        new StdOperation(StandardOperation.BV2BOOL, ArityRange.UNARY) {
          @Override
          public Data calculate(final Data... operands) {
            return Data.newBoolean(operands[0].getBitVector().equals(BitVector.TRUE));
          }

          @Override
          public boolean validTypes(final Data... operands) {
            return operands[0].isType(DataType.bitVector(1));
          }
        });

    return OperationGroup.operationMap(StandardOperation.class, operations);
  }

  private static BitVector bvarg(final Data[] operands, final int num) {
    return operands[num].getBitVector();
  }

  public static Map<StandardOperation, Operation<StandardOperation>> realOps() {
    final List<Operation<StandardOperation>> operations = new ArrayList<>();

    operations.addAll(Arrays.<Operation<StandardOperation>>asList(
        new StdOperation(StandardOperation.PLUS, ArityRange.UNARY) {
          @Override
          public Data calculate(final Data... operands) {
            return operands[0];
          }
        },

        new StdOperation(StandardOperation.MINUS, ArityRange.UNARY) {
          @Override
          public Data calculate(final Data... operands) {
            return Data.newReal(-operands[0].getReal());
          }
        },

        new StdOperation(StandardOperation.ADD, ArityRange.BINARY_UNBOUNDED) {
          @Override
          public Data calculate(final Data... operands) {
            double result = operands[0].getReal();
            for (int index = 1; index < operands.length; ++index) {
              result += operands[index].getReal();
            }
            return Data.newReal(result);
          }
        },

        new StdOperation(StandardOperation.SUB, ArityRange.BINARY_UNBOUNDED) {
          @Override
          public Data calculate(final Data... operands) {
            double result = operands[0].getReal();
            for (int index = 1; index < operands.length; ++index) {
              result -= operands[index].getReal();
            }
            return Data.newReal(result);
          }
        },

        new StdOperation(StandardOperation.MUL, ArityRange.BINARY_UNBOUNDED) {
          @Override
          public Data calculate(final Data... operands) {
            double result = operands[0].getReal();
            for (int index = 1; index < operands.length; ++index) {
              result *= operands[index].getReal();
            }
            return Data.newReal(result);
          }
        },

        new StdOperation(StandardOperation.DIV, ArityRange.BINARY) {
          @Override
          public Data calculate(final Data... operands) {
            final double value1 = operands[0].getReal();
            final double value2 = operands[1].getReal();

            return Data.newReal(value1 / value2);
          }
        },

        new StdOperation(StandardOperation.ABS, ArityRange.UNARY) {
          @Override
          public Data calculate(final Data... operands) {
            final double value = operands[0].getReal();
            if (value < 0) {
              return Data.newReal(-value);
            }
            return operands[0];
          }
        }));
    operations.addAll(ordered(Double.class));

    return OperationGroup.operationMap(StandardOperation.class, operations);
  }

  public static <T extends Comparable<T>>
      List<Operation<StandardOperation>> ordered(final Class<T> clazz) {
    return Arrays.<Operation<StandardOperation>>asList(
        new StdOperation(StandardOperation.GREATER, ArityRange.BINARY) {
          @Override
          public Data calculate(final Data... operands) {
            return Data.newBoolean(compare(clazz, operands[0], operands[1]) > 0);
          }
        },

        new StdOperation(StandardOperation.GREATEREQ, ArityRange.BINARY) {
          @Override
          public Data calculate(final Data... operands) {
            return Data.newBoolean(compare(clazz, operands[0], operands[1]) >= 0);
          }
        },

        new StdOperation(StandardOperation.LESS, ArityRange.BINARY) {
          @Override
          public Data calculate(final Data... operands) {
            return Data.newBoolean(compare(clazz, operands[0], operands[1]) < 0);
          }
        },

        new StdOperation(StandardOperation.LESSEQ, ArityRange.BINARY) {
          @Override
          public Data calculate(final Data... operands) {
            return Data.newBoolean(compare(clazz, operands[0], operands[1]) <= 0);
          }
        },

        new StdOperation(StandardOperation.MAX, ArityRange.UNARY_UNBOUNDED) {
          @Override
          public Data calculate(final Data... operands) {
            Data value = operands[0];
            for (int i = 1; i < operands.length; ++i) {
              if (compare(clazz, operands[i], value) > 0) {
                value = operands[i];
              }
            }
            return value;
          }
        },

        new StdOperation(StandardOperation.MIN, ArityRange.UNARY_UNBOUNDED) {
          @Override
          public Data calculate(final Data... operands) {
            Data value = operands[0];
            for (int i = 1; i < operands.length; ++i) {
              if (compare(clazz, operands[i], value) < 0) {
                value = operands[i];
              }
            }
            return value;
          }
        });
  }

  private static <T extends Comparable<T>>
      int compare(final Class<T> clazz, final Data lhs, final Data rhs) {
    return lhs.getValue(clazz).compareTo(rhs.getValue(clazz));
  }
}
