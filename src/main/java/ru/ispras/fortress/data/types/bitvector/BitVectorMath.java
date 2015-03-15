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

package ru.ispras.fortress.data.types.bitvector;

import static ru.ispras.fortress.util.InvariantChecks.checkNotNull;
import static ru.ispras.fortress.data.types.bitvector.BitVectorMath.Operands.*;

import java.math.BigInteger;

/**
 * The {@code BitVectorMath} class contains utility methods and classes to perform operations
 * with bit vectors. 
 * 
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */

public final class BitVectorMath {
  private BitVectorMath() {}

  /**
   * Describes the number of arguments accepted by the bit vector operations. 
   */

  public static enum Operands {
    UNARY(1), BINARY(2), TERNARY(3);

    private final int count;

    private Operands(int count) {
      this.count = count;
    }

    public int count() {
      return count;
    }
  }

  /**
   * Provides singleton objects that allow performing operations with bit vectors in
   * a unified way (i.e. polymorphically).
   */

  public static enum Operations {

    AND(BINARY) {
      @Override
      public BitVector execute(BitVector lhs, BitVector rhs) {
        return and(lhs, rhs);
      }
    },

    OR(BINARY) {
      @Override
      public BitVector execute(BitVector lhs, BitVector rhs) {
        return or(lhs, rhs);
      }
    },

    XOR(BINARY) {
      @Override
      public BitVector execute(BitVector lhs, BitVector rhs) {
        return xor(lhs, rhs);
      }
    },

    NOT(UNARY) {
      @Override
      public BitVector execute(BitVector v) {
        return not(v);
      }
    },

    NAND(BINARY) {
      @Override
      public BitVector execute(BitVector lhs, BitVector rhs) {
        return nand(lhs, rhs);
      }
    },

    NOR(BINARY) {
      @Override
      public BitVector execute(BitVector lhs, BitVector rhs) {
        return nor(lhs, rhs);
      }
    },

    XNOR(BINARY) {
      @Override
      public BitVector execute(BitVector lhs, BitVector rhs) {
        return xnor(lhs, rhs);
      }
    },

    SHL(BINARY) {
      @Override
      public BitVector execute(BitVector lhs, BitVector rhs) {
        return shl(lhs, rhs);
      }
    },

    LSHR(BINARY) {
      @Override
      public BitVector execute(BitVector lhs, BitVector rhs) {
        return lshr(lhs, rhs);
      }
    },

    ASHR(BINARY) {
      @Override
      public BitVector execute(BitVector lhs, BitVector rhs) {
        return ashr(lhs, rhs);
      }
    },

    ROTL(BINARY) {
      @Override
      public BitVector execute(BitVector lhs, BitVector rhs) {
        return rotl(lhs, rhs);
      }
    },

    ROTR(BINARY) {
      @Override
      public BitVector execute(BitVector lhs, BitVector rhs) {
        return rotr(lhs, rhs);
      }
    },

    ADD(BINARY) {
      @Override
      public BitVector execute(BitVector lhs, BitVector rhs) {
        return add(lhs, rhs);
      }
    },

    SUB(BINARY) {
      @Override
      public BitVector execute(BitVector lhs, BitVector rhs) {
        return sub(lhs, rhs);
      }
    },

    PLUS(UNARY) {
      @Override
      public BitVector execute(BitVector v) {
        return plus(v);
      }
    },

    NEG(UNARY) {
      @Override
      public BitVector execute(BitVector v) {
        return neg(v);
      }
    },

    ULE(BINARY) {
      @Override
      public BitVector execute(BitVector lhs, BitVector rhs) {
        return ule(lhs, rhs);
      }
    },

    ULT(BINARY) {
      @Override
      public BitVector execute(BitVector lhs, BitVector rhs) {
        return ult(lhs, rhs);
      }
    },

    UGE(BINARY) {
      @Override
      public BitVector execute(BitVector lhs, BitVector rhs) {
        return uge(lhs, rhs);
      }
    },

    UGT(BINARY) {
      @Override
      public BitVector execute(BitVector lhs, BitVector rhs) {
        return ugt(lhs, rhs);
      }
    },

    SLE(BINARY) {
      @Override
      public BitVector execute(BitVector lhs, BitVector rhs) {
        return sle(lhs, rhs);
      }
    },

    SLT(BINARY) {
      @Override
      public BitVector execute(BitVector lhs, BitVector rhs) {
        return slt(lhs, rhs);
      }
    },

    SGE(BINARY) {
      @Override
      public BitVector execute(BitVector lhs, BitVector rhs) {
        return sge(lhs, rhs);
      }
    },

    SGT(BINARY) {
      @Override
      public BitVector execute(BitVector lhs, BitVector rhs) {
        return sgt(lhs, rhs);
      }
    },

    EQ(BINARY) {
      @Override
      public BitVector execute(BitVector lhs, BitVector rhs) {
        return eq(lhs, rhs);
      }
    },

    NEQ(BINARY) {
      @Override
      public BitVector execute(BitVector lhs, BitVector rhs) {
        return neq(lhs, rhs);
      }
    };

    private final Operands operands;

    private Operations(Operands operands) {
      this.operands = operands;
    }

    public Operands getOperands() {
      return operands;
    }

    // IMPORTANT: must be overridden if supported by a specific operation.
    public BitVector execute(BitVector v) {
      throw new UnsupportedOperationException(String.format(
        "Unary %s operation is not supported", name()));
    }

    // IMPORTANT: must be overridden if supported by a specific operation.
    public BitVector execute(BitVector lhs, BitVector rhs) {
      throw new UnsupportedOperationException(String.format(
        "Binary %s operation is not supported", name()));
    }
  }

  public static BitVector and(BitVector lhs, BitVector rhs) {
    return transform(lhs, rhs, BitVectorAlgorithm.BinaryOperation.AND);
  }

  public static BitVector or(BitVector lhs, BitVector rhs) {
    return transform(lhs, rhs, BitVectorAlgorithm.BinaryOperation.OR);
  }

  public static BitVector xor(BitVector lhs, BitVector rhs) {
    return transform(lhs, rhs, BitVectorAlgorithm.BinaryOperation.XOR);
  }

  public static BitVector not(BitVector v) {
    return transform(v, BitVectorAlgorithm.UnaryOperation.NOT);
  }

  public static BitVector nand(BitVector lhs, BitVector rhs) {
    return not(and(lhs, rhs));
  }

  public static BitVector nor(BitVector lhs, BitVector rhs) {
    return not(or(lhs, rhs));
  }

  public static BitVector xnor(BitVector lhs, BitVector rhs) {
    return not(xor(lhs, rhs));
  }

  /**
   * Performs logical left shift of the specified bit vector by the specified shift amount.
   * The actual shift amount is calculated as {@code to} modulo {@code v.getBitSize()}. If the 
   * actual shift amount equals {@code 0}, no shift is performed and the initial bit vector is
   * returned. Otherwise, a new copy of data is created and returned. If the shift amount is
   * negative, the actual shift amount is calculated as {@code v.getBitSize()} minus 
   * ({@code to} modulo {@code v.getBitSize()}).
   * 
   * @param v Bit vector to be shifted.
   * @param to Shift amount.
   * @return Logical left shift result.
   * 
   * @throws NullPointerException if any of the parameters is {@code null}.
   */

  public static BitVector shl(BitVector v, BitVector to) {
    checkNotNull(v);
    checkNotNull(to);

    return shl(v, to.bigIntegerValue());
  }

  public static BitVector shl(BitVector v, BigInteger to) {
    checkNotNull(v);
    checkNotNull(to);

    final BigInteger size = BigInteger.valueOf(v.getBitSize());
    final BigInteger amount = to.mod(size);

    return shl_internal(v, amount.intValue());
  }

  public static BitVector shl(BitVector v, int to) {
    checkNotNull(v);

    final int amount = to % v.getBitSize();
    return shl_internal(v, amount);
  }

  private static BitVector shl_internal(BitVector v, int amount) {
    if (0 == amount) {
      return v;
    }

    final int distance = Math.abs(amount);
    final BitVector result = BitVector.newEmpty(v.getBitSize());

    if (amount > 0) {
      BitVectorAlgorithm.copy(v, 0, result, distance, result.getBitSize() - distance);
    } else {
      BitVectorAlgorithm.copy(v, 0, result, result.getBitSize() - distance, distance);
    }

    return result;
  }

  /**
   * Performs logical right shift of the specified bit vector by the specified shift amount.
   * The actual shift amount is calculated as {@code to} modulo {@code v.getBitSize()}. If the 
   * actual shift amount equals {@code 0}, no shift is performed and the initial bit vector is
   * returned. Otherwise, a new copy of data is created and returned. If the shift amount is
   * negative, the actual shift amount is calculated as {@code v.getBitSize()} minus 
   * ({@code to} modulo {@code v.getBitSize()}).
   * 
   * @param v Bit vector to be shifted.
   * @param to Shift amount.
   * @return Logical right shift result.
   * 
   * @throws NullPointerException if any of the parameters is {@code null}.
   */

  public static BitVector lshr(BitVector v, BitVector to) {
    checkNotNull(v);
    checkNotNull(to);

    return lshr(v, to.bigIntegerValue());
  }

  public static BitVector lshr(BitVector v, BigInteger to) {
    checkNotNull(v);
    checkNotNull(to);

    final BigInteger size = BigInteger.valueOf(v.getBitSize());
    final BigInteger amount = to.mod(size);

    return lshr_internal(v, amount.intValue());
  }

  public static BitVector lshr(BitVector v, int to) {
    checkNotNull(v);

    final int amount = to % v.getBitSize();
    return lshr_internal(v, amount);
  }

  private static BitVector lshr_internal(BitVector v, int amount) {
    if (0 == amount) {
      return v;
    }

    final int distance = Math.abs(amount);
    final BitVector result = BitVector.newEmpty(v.getBitSize());

    if (amount > 0) {
      BitVectorAlgorithm.copy(v, distance, result, 0, result.getBitSize() - distance);
    } else {
      BitVectorAlgorithm.copy(v, result.getBitSize() - distance, result, 0, distance);
    }

    return result;
  }

  /**
   * Performs arithmetical right shift of the specified bit vector by the specified shift amount.
   * The actual shift amount is calculated as {@code to} modulo {@code v.getBitSize()}. If the 
   * actual shift amount equals {@code 0}, no shift is performed and the initial bit vector is
   * returned. Otherwise, a new copy of data is created and returned. If the shift amount is
   * negative, the actual shift amount is calculated as {@code v.getBitSize()} minus 
   * ({@code to} modulo {@code v.getBitSize()}).
   * 
   * @param v Bit vector to be shifted.
   * @param to Shift amount.
   * @return Arithmetical right shift result.
   * 
   * @throws NullPointerException if any of the parameters is {@code null}.
   */

  public static BitVector ashr(BitVector v, BitVector to) {
    checkNotNull(v);
    checkNotNull(to);
    
    return ashr(v, to.bigIntegerValue());
  }

  public static BitVector ashr(BitVector v, BigInteger to) {
    checkNotNull(v);
    checkNotNull(to);

    final BigInteger size = BigInteger.valueOf(v.getBitSize());
    final BigInteger amount = to.mod(size);

    return ashr_internal(v, amount.intValue());
  }

  public static BitVector ashr(BitVector v, int to) {
    checkNotNull(v);

    final int amount = to % v.getBitSize();
    return ashr_internal(v, amount);
  }

  private static BitVector ashr_internal(BitVector v, int amount) {
    if (0 == amount) {
      return v;
    }

    final int distance = Math.abs(amount);
    final BitVector result = BitVector.newEmpty(v.getBitSize());

    // If the sign (most significant) bit is set, fill the result with 1s.
    if (v.getBit(v.getBitSize() - 1)) {
      BitVectorAlgorithm.fill(result, (byte) 0xFF);
    }

    if (amount > 0) {
      BitVectorAlgorithm.copy(v, distance, result, 0, result.getBitSize() - distance);
    } else {
      BitVectorAlgorithm.copy(v, result.getBitSize() - distance, result, 0, distance);
    }

    return result;
  }


  public static BitVector rotl(BitVector v, int to) {
    checkNotNull(v);

    final int distance = Math.abs(to % v.getBitSize());
    if (0 == distance) {
      return v;
    }

    final BitVector result = BitVector.newEmpty(v.getBitSize());

    if (to > 0) {
      BitVectorAlgorithm.copy(v, 0, result, distance, result.getBitSize() - distance);
      BitVectorAlgorithm.copy(v, v.getBitSize() - distance, result, 0, distance);
    } else {
      BitVectorAlgorithm.copy(v, 0, result, result.getBitSize() - distance, distance);
      BitVectorAlgorithm.copy(v, distance, result, 0, result.getBitSize() - distance);
    }

    return result;
  }

  public static BitVector rotl(BitVector v, BitVector to) {
    checkNotNull(v);
    checkNotNull(to);

    return rotl(v, to.intValue());
  }

  public static BitVector rotr(BitVector v, int to) {
    checkNotNull(v);

    final int distance = Math.abs(to % v.getBitSize());
    if (0 == distance) {
      return v;
    }

    final BitVector result = BitVector.newEmpty(v.getBitSize());

    if (to > 0) {
      BitVectorAlgorithm.copy(v, distance, result, 0, result.getBitSize() - distance);
      BitVectorAlgorithm.copy(v, 0, result, result.getBitSize() - distance, distance);
    } else {
      BitVectorAlgorithm.copy(v, result.getBitSize() - distance, result, 0, distance);
      BitVectorAlgorithm.copy(v, 0, result, distance, result.getBitSize() - distance);
    }

    return result;
  }

  public static BitVector rotr(BitVector v, BitVector to) {
    checkNotNull(v);
    checkNotNull(to);

    return rotr(v, to.intValue());
  }

  public static BitVector add(BitVector lhs, BitVector rhs) {
    return transform(lhs, rhs, new BitVectorAlgorithm.IBinaryOperation() {
      private byte carry = 0;

      @Override
      public byte run(byte lhs, byte rhs) {
        final int sum = (lhs & 0xFF) + (rhs & 0xFF) + (carry & 0xFF);
        carry = (byte) (sum >>> BitVector.BITS_IN_BYTE);
        return (byte) sum;
      }
    });
  }

  public static BitVector sub(BitVector lhs, BitVector rhs) {
    return add(lhs, neg(rhs));
  }

  public static BitVector plus(BitVector v) {
    checkNotNull(v);
    return v;
  }

  public static BitVector neg(BitVector v) {
    checkNotNull(v);
    // Negation algorithm: "-arg = ~arg + 1".
    return add(not(v), BitVector.valueOf(1, v.getBitSize()));
  }

  public static BitVector ule(BitVector lhs, BitVector rhs) {
    checkNotNull(lhs);
    checkNotNull(rhs);
    checkEqualSize(lhs, rhs);

    return BitVector.valueOf(lhs.compareTo(rhs) <= 0);
  }

  public static BitVector ult(BitVector lhs, BitVector rhs) {
    checkNotNull(lhs);
    checkNotNull(rhs);
    checkEqualSize(lhs, rhs);

    return BitVector.valueOf(lhs.compareTo(rhs) < 0);
  }

  public static BitVector uge(BitVector lhs, BitVector rhs) {
    checkNotNull(lhs);
    checkNotNull(rhs);
    checkEqualSize(lhs, rhs);

    return BitVector.valueOf(lhs.compareTo(rhs) >= 0);
  }

  public static BitVector ugt(BitVector lhs, BitVector rhs) {
    checkNotNull(lhs);
    checkNotNull(rhs);
    checkEqualSize(lhs, rhs);

    return BitVector.valueOf(lhs.compareTo(rhs) > 0);
  }

  public static BitVector sle(BitVector lhs, BitVector rhs) {
    checkNotNull(lhs);
    checkNotNull(rhs);
    checkEqualSize(lhs, rhs);

    final int signBitIndex = lhs.getBitSize() - 1;

    final boolean isLeftNeg = lhs.getBit(signBitIndex);
    final boolean isRightNeg = rhs.getBit(signBitIndex);

    if (isLeftNeg != isRightNeg) {
      // If lhs is negative, it is less. Otherwise, it is greater.
      return BitVector.valueOf(isLeftNeg);
    }

    return BitVector.valueOf(lhs.compareTo(rhs) <= 0);
  }

  public static BitVector slt(BitVector lhs, BitVector rhs) {
    checkNotNull(lhs);
    checkNotNull(rhs);
    checkEqualSize(lhs, rhs);

    final int signBitIndex = lhs.getBitSize() - 1;

    final boolean isLeftNeg = lhs.getBit(signBitIndex);
    final boolean isRightNeg = rhs.getBit(signBitIndex);

    if (isLeftNeg != isRightNeg) {
      // If lhs is negative, it is less. Otherwise, it is greater.
      return BitVector.valueOf(isLeftNeg); 
    }

    return BitVector.valueOf(lhs.compareTo(rhs) < 0);
  }

  public static BitVector sge(BitVector lhs, BitVector rhs) {
    checkNotNull(lhs);
    checkNotNull(rhs);
    checkEqualSize(lhs, rhs);

    final int signBitIndex = lhs.getBitSize() - 1;

    final boolean isLeftNeg = lhs.getBit(signBitIndex);
    final boolean isRightNeg = rhs.getBit(signBitIndex);

    if (isLeftNeg != isRightNeg) {
      // If lhs is positive, it is greater. Otherwise, it is less.
      return BitVector.valueOf(!isLeftNeg); 
    }

    return BitVector.valueOf(lhs.compareTo(rhs) >= 0);
  }

  public static BitVector sgt(BitVector lhs, BitVector rhs) {
    checkNotNull(lhs);
    checkNotNull(rhs);
    checkEqualSize(lhs, rhs);

    final int signBitIndex = lhs.getBitSize() - 1;

    final boolean isLeftNeg = lhs.getBit(signBitIndex);
    final boolean isRightNeg = rhs.getBit(signBitIndex);

    if (isLeftNeg != isRightNeg) {
      // If lhs is positive, it is greater. Otherwise, it is less.
      return BitVector.valueOf(!isLeftNeg); 
    }

    return BitVector.valueOf(lhs.compareTo(rhs) > 0);
  }

  public static BitVector eq(BitVector lhs, BitVector rhs) {
    checkNotNull(lhs);
    checkNotNull(rhs);
    checkEqualSize(lhs, rhs);

    return BitVector.valueOf(lhs.equals(rhs));
  }

  public static BitVector neq(BitVector lhs, BitVector rhs) {
    checkNotNull(lhs);
    checkNotNull(rhs);
    checkEqualSize(lhs, rhs);

    return BitVector.valueOf(!lhs.equals(rhs));
  }

  private static BitVector transform(BitVector lhs, BitVector rhs,
      BitVectorAlgorithm.IBinaryOperation op) {
    checkNotNull(lhs);
    checkNotNull(rhs);
    checkEqualSize(lhs, rhs);

    final BitVector result = BitVector.newEmpty(lhs.getBitSize());
    BitVectorAlgorithm.transform(lhs, rhs, result, op);

    return result;
  }

  private static BitVector transform(BitVector v, BitVectorAlgorithm.IUnaryOperation op) {
    checkNotNull(v);

    final BitVector result = BitVector.newEmpty(v.getBitSize());
    BitVectorAlgorithm.transform(v, result, op);

    return result;
  }

  private static void checkEqualSize(BitVector lhs, BitVector rhs) {
    if (lhs.getBitSize() != rhs.getBitSize()) {
      throw new IllegalArgumentException(String.format(
        "Bit vector sizes do not match: %d != %d.", lhs.getBitSize(), rhs.getBitSize()));
    }
  }
}
