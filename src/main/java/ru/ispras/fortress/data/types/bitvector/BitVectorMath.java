/*
 * Copyright 2014-2016 ISP RAS (http://www.ispras.ru)
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

import static ru.ispras.fortress.data.types.bitvector.BitVectorMath.Operands.BINARY;
import static ru.ispras.fortress.data.types.bitvector.BitVectorMath.Operands.UNARY;

import ru.ispras.fortress.util.InvariantChecks;

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

    private Operands(final int count) {
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
      public BitVector execute(final BitVector lhs, final BitVector rhs) {
        return and(lhs, rhs);
      }
    },

    OR(BINARY) {
      @Override
      public BitVector execute(final BitVector lhs, final BitVector rhs) {
        return or(lhs, rhs);
      }
    },

    XOR(BINARY) {
      @Override
      public BitVector execute(final BitVector lhs, final BitVector rhs) {
        return xor(lhs, rhs);
      }
    },

    NOT(UNARY) {
      @Override
      public BitVector execute(final BitVector bitVector) {
        return not(bitVector);
      }
    },

    NAND(BINARY) {
      @Override
      public BitVector execute(final BitVector lhs, final BitVector rhs) {
        return nand(lhs, rhs);
      }
    },

    NOR(BINARY) {
      @Override
      public BitVector execute(final BitVector lhs, final BitVector rhs) {
        return nor(lhs, rhs);
      }
    },

    XNOR(BINARY) {
      @Override
      public BitVector execute(final BitVector lhs, final BitVector rhs) {
        return xnor(lhs, rhs);
      }
    },

    SHL(BINARY) {
      @Override
      public BitVector execute(final BitVector lhs, final BitVector rhs) {
        return shl(lhs, rhs);
      }
    },

    USHL(BINARY) {
      @Override
      public BitVector execute(final BitVector lhs, final BitVector rhs) {
        if (rhs.bigIntegerValue(false).compareTo(BigInteger.valueOf(lhs.getBitSize())) >= 0) {
          return BitVector.valueOf(0, lhs.getBitSize());
        }
        return shl(lhs, rhs);
      }
    },

    LSHR(BINARY) {
      @Override
      public BitVector execute(final BitVector lhs, final BitVector rhs) {
        return lshr(lhs, rhs);
      }
    },

    ASHR(BINARY) {
      @Override
      public BitVector execute(final BitVector lhs, final BitVector rhs) {
        return ashr(lhs, rhs);
      }
    },

    ROTL(BINARY) {
      @Override
      public BitVector execute(final BitVector lhs, final BitVector rhs) {
        return rotl(lhs, rhs);
      }
    },

    ROTR(BINARY) {
      @Override
      public BitVector execute(final BitVector lhs, final BitVector rhs) {
        return rotr(lhs, rhs);
      }
    },

    ADD(BINARY) {
      @Override
      public BitVector execute(final BitVector lhs, final BitVector rhs) {
        return add(lhs, rhs);
      }
    },

    SUB(BINARY) {
      @Override
      public BitVector execute(final BitVector lhs, final BitVector rhs) {
        return sub(lhs, rhs);
      }
    },

    MUL(BINARY) {
      @Override
      public BitVector execute(final BitVector lhs, final BitVector rhs) {
        return mul(lhs, rhs);
      }
    },

    UDIV(BINARY) {
      @Override
      public BitVector execute(final BitVector lhs, final BitVector rhs) {
        return udiv(lhs, rhs);
      }
    },

    SDIV(BINARY) {
      @Override
      public BitVector execute(final BitVector lhs, final BitVector rhs) {
        return sdiv(lhs, rhs);
      }
    },

    UREM(BINARY) {
      @Override
      public BitVector execute(final BitVector lhs, final BitVector rhs) {
        return urem(lhs, rhs);
      }
    },

    SREM(BINARY) {
      @Override
      public BitVector execute(final BitVector lhs, final BitVector rhs) {
        return srem(lhs, rhs);
      }
    },

    SMOD(BINARY) {
      @Override
      public BitVector execute(final BitVector lhs, final BitVector rhs) {
        return smod(lhs, rhs);
      }
    },

    PLUS(UNARY) {
      @Override
      public BitVector execute(final BitVector bitVector) {
        return plus(bitVector);
      }
    },

    NEG(UNARY) {
      @Override
      public BitVector execute(final BitVector bitVector) {
        return neg(bitVector);
      }
    },

    ULE(BINARY) {
      @Override
      public BitVector execute(final BitVector lhs, final BitVector rhs) {
        return BitVector.valueOf(ule(lhs, rhs));
      }
    },

    ULT(BINARY) {
      @Override
      public BitVector execute(final BitVector lhs, final BitVector rhs) {
        return BitVector.valueOf(ult(lhs, rhs));
      }
    },

    UGE(BINARY) {
      @Override
      public BitVector execute(final BitVector lhs, final BitVector rhs) {
        return BitVector.valueOf(uge(lhs, rhs));
      }
    },

    UGT(BINARY) {
      @Override
      public BitVector execute(final BitVector lhs, final BitVector rhs) {
        return BitVector.valueOf(ugt(lhs, rhs));
      }
    },

    SLE(BINARY) {
      @Override
      public BitVector execute(final BitVector lhs, final BitVector rhs) {
        return BitVector.valueOf(sle(lhs, rhs));
      }
    },

    SLT(BINARY) {
      @Override
      public BitVector execute(final BitVector lhs, final BitVector rhs) {
        return BitVector.valueOf(slt(lhs, rhs));
      }
    },

    SGE(BINARY) {
      @Override
      public BitVector execute(final BitVector lhs, final BitVector rhs) {
        return BitVector.valueOf(sge(lhs, rhs));
      }
    },

    SGT(BINARY) {
      @Override
      public BitVector execute(final BitVector lhs, final BitVector rhs) {
        return BitVector.valueOf(sgt(lhs, rhs));
      }
    },

    EQ(BINARY) {
      @Override
      public BitVector execute(final BitVector lhs, final BitVector rhs) {
        return BitVector.valueOf(eq(lhs, rhs));
      }
    },

    NEQ(BINARY) {
      @Override
      public BitVector execute(final BitVector lhs, final BitVector rhs) {
        return BitVector.valueOf(neq(lhs, rhs));
      }
    },

    ANDR(UNARY) {
      @Override
      public BitVector execute(final BitVector bitVector) {
        return andr(bitVector);
      }
    },

    NANDR(UNARY) {
      @Override
      public BitVector execute(final BitVector bitVector) {
        return nandr(bitVector);
      }
    },

    ORR(UNARY) {
      @Override
      public BitVector execute(final BitVector bitVector) {
        return orr(bitVector);
      }
    },

    NORR(UNARY) {
      @Override
      public BitVector execute(final BitVector bitVector) {
        return norr(bitVector);
      }
    },

    XORR(UNARY) {
      @Override
      public BitVector execute(final BitVector bitVector) {
        return xorr(bitVector);
      }
    },

    XNORR(UNARY) {
      @Override
      public BitVector execute(final BitVector bitVector) {
        return xnorr(bitVector);
      }
    };

    private final Operands operands;

    private Operations(final Operands operands) {
      this.operands = operands;
    }

    public Operands getOperands() {
      return operands;
    }

    // IMPORTANT: must be overridden if supported by a specific operation.
    public BitVector execute(final BitVector bitVector) {
      throw new UnsupportedOperationException(String.format(
        "Unary %s operation is not supported", name()));
    }

    // IMPORTANT: must be overridden if supported by a specific operation.
    public BitVector execute(final BitVector lhs, final BitVector rhs) {
      throw new UnsupportedOperationException(String.format(
        "Binary %s operation is not supported", name()));
    }
  }

  public static BitVector and(final BitVector lhs, final BitVector rhs) {
    return transform(lhs, rhs, BitVectorAlgorithm.BinaryOperation.AND);
  }

  public static BitVector or(final BitVector lhs, final BitVector rhs) {
    return transform(lhs, rhs, BitVectorAlgorithm.BinaryOperation.OR);
  }

  public static BitVector xor(final BitVector lhs, final BitVector rhs) {
    return transform(lhs, rhs, BitVectorAlgorithm.BinaryOperation.XOR);
  }

  public static BitVector not(final BitVector bitVector) {
    return transform(bitVector, BitVectorAlgorithm.UnaryOperation.NOT);
  }

  public static BitVector nand(final BitVector lhs, final BitVector rhs) {
    return not(and(lhs, rhs));
  }

  public static BitVector nor(final BitVector lhs, final BitVector rhs) {
    return not(or(lhs, rhs));
  }

  public static BitVector xnor(final BitVector lhs, final BitVector rhs) {
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
   * @param bitVector Bit vector to be shifted.
   * @param to Shift amount.
   * @return Logical left shift result.
   *
   * @throws IllegalArgumentException if any of the parameters is {@code null}.
   */
  public static BitVector shl(final BitVector bitVector, final BitVector to) {
    InvariantChecks.checkNotNull(bitVector);
    InvariantChecks.checkNotNull(to);

    return shl(bitVector, to.bigIntegerValue());
  }

  public static BitVector shl(final BitVector bitVector, final BigInteger to) {
    InvariantChecks.checkNotNull(bitVector);
    InvariantChecks.checkNotNull(to);

    final BigInteger size = BigInteger.valueOf(bitVector.getBitSize());
    final BigInteger amount = to.mod(size);

    return doShl(bitVector, amount.intValue());
  }

  public static BitVector shl(final BitVector bitVector, final int to) {
    InvariantChecks.checkNotNull(bitVector);

    final int amount = to % bitVector.getBitSize();
    return doShl(bitVector, amount);
  }

  private static BitVector doShl(final BitVector bitVector, final int amount) {
    if (0 == amount) {
      return bitVector;
    }

    final int distance = Math.abs(amount);
    final BitVector result = BitVector.newEmpty(bitVector.getBitSize());

    if (amount > 0) {
      BitVectorAlgorithm.copy(bitVector, 0, result, distance, result.getBitSize() - distance);
    } else {
      BitVectorAlgorithm.copy(bitVector, 0, result, result.getBitSize() - distance, distance);
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
   * @param bitVector Bit vector to be shifted.
   * @param to Shift amount.
   * @return Logical right shift result.
   *
   * @throws IllegalArgumentException if any of the parameters is {@code null}.
   */
  public static BitVector lshr(final BitVector bitVector, final BitVector to) {
    InvariantChecks.checkNotNull(bitVector);
    InvariantChecks.checkNotNull(to);

    return lshr(bitVector, to.bigIntegerValue());
  }

  public static BitVector lshr(final BitVector bitVector, final BigInteger to) {
    InvariantChecks.checkNotNull(bitVector);
    InvariantChecks.checkNotNull(to);

    final BigInteger size = BigInteger.valueOf(bitVector.getBitSize());
    final BigInteger amount = to.mod(size);

    return doLshr(bitVector, amount.intValue());
  }

  public static BitVector lshr(final BitVector bitVector, final int to) {
    InvariantChecks.checkNotNull(bitVector);

    final int amount = to % bitVector.getBitSize();
    return doLshr(bitVector, amount);
  }

  private static BitVector doLshr(final BitVector bitVector, final int amount) {
    if (0 == amount) {
      return bitVector;
    }

    final int distance = Math.abs(amount);
    final BitVector result = BitVector.newEmpty(bitVector.getBitSize());

    if (amount > 0) {
      BitVectorAlgorithm.copy(bitVector, distance, result, 0, result.getBitSize() - distance);
    } else {
      BitVectorAlgorithm.copy(bitVector, result.getBitSize() - distance, result, 0, distance);
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
   * @param bitVector Bit vector to be shifted.
   * @param to Shift amount.
   * @return Arithmetical right shift result.
   *
   * @throws IllegalArgumentException if any of the parameters is {@code null}.
   */
  public static BitVector ashr(final BitVector bitVector, final BitVector to) {
    InvariantChecks.checkNotNull(bitVector);
    InvariantChecks.checkNotNull(to);

    return ashr(bitVector, to.bigIntegerValue());
  }

  public static BitVector ashr(final BitVector bitVector, final BigInteger to) {
    InvariantChecks.checkNotNull(bitVector);
    InvariantChecks.checkNotNull(to);

    final BigInteger size = BigInteger.valueOf(bitVector.getBitSize());
    final BigInteger amount = to.mod(size);

    return doAshr(bitVector, amount.intValue());
  }

  public static BitVector ashr(final BitVector bitVector, final int to) {
    InvariantChecks.checkNotNull(bitVector);

    final int amount = to % bitVector.getBitSize();
    return doAshr(bitVector, amount);
  }

  private static BitVector doAshr(final BitVector bitVector, final int amount) {
    if (0 == amount) {
      return bitVector;
    }

    final int distance = Math.abs(amount);
    final BitVector result = BitVector.newEmpty(bitVector.getBitSize());

    // If the sign (most significant) bit is set, fill the result with 1s.
    if (bitVector.getBit(bitVector.getBitSize() - 1)) {
      BitVectorAlgorithm.fill(result, (byte) 0xFF);
    }

    if (amount > 0) {
      BitVectorAlgorithm.copy(bitVector, distance, result, 0, result.getBitSize() - distance);
    } else {
      BitVectorAlgorithm.copy(bitVector, result.getBitSize() - distance, result, 0, distance);
    }

    return result;
  }

  /**
   * Performs rotation to the left of the specified bit vector by the specified shift amount.
   * The actual shift amount is calculated as {@code to} modulo {@code v.getBitSize()}. If the
   * actual shift amount equals {@code 0}, no shift is performed and the initial bit vector is
   * returned. Otherwise, a new copy of data is created and returned. If the shift amount is
   * negative, the actual shift amount is calculated as {@code v.getBitSize()} minus
   * ({@code to} modulo {@code v.getBitSize()}).
   *
   * @param bitVector Bit vector to be shifted.
   * @param to Shift amount.
   * @return Left rotation result.
   *
   * @throws IllegalArgumentException if any of the parameters is {@code null}.
   */
  public static BitVector rotl(final BitVector bitVector, final BitVector to) {
    InvariantChecks.checkNotNull(bitVector);
    InvariantChecks.checkNotNull(to);

    return rotl(bitVector, to.bigIntegerValue());
  }

  public static BitVector rotl(final BitVector bitVector, final BigInteger to) {
    InvariantChecks.checkNotNull(bitVector);
    InvariantChecks.checkNotNull(to);

    final BigInteger size = BigInteger.valueOf(bitVector.getBitSize());
    final BigInteger amount = to.mod(size);

    return doRotl(bitVector, amount.intValue());
  }

  public static BitVector rotl(final BitVector bitVector, final int to) {
    InvariantChecks.checkNotNull(bitVector);

    final int distance = Math.abs(to % bitVector.getBitSize());
    if (0 == distance) {
      return bitVector;
    }

    final BitVector result = BitVector.newEmpty(bitVector.getBitSize());

    if (to > 0) {
      BitVectorAlgorithm.copy(bitVector, 0, result, distance, result.getBitSize() - distance);
      BitVectorAlgorithm.copy(bitVector, bitVector.getBitSize() - distance, result, 0, distance);
    } else {
      BitVectorAlgorithm.copy(bitVector, 0, result, result.getBitSize() - distance, distance);
      BitVectorAlgorithm.copy(bitVector, distance, result, 0, result.getBitSize() - distance);
    }

    return result;
  }

  private static BitVector doRotl(final BitVector bitVector, final int amount) {
    if (0 == amount) {
      return bitVector;
    }

    final int distance = Math.abs(amount);
    final BitVector result = BitVector.newEmpty(bitVector.getBitSize());

    if (amount > 0) {
      BitVectorAlgorithm.copy(bitVector, 0, result, distance, result.getBitSize() - distance);
      BitVectorAlgorithm.copy(bitVector, bitVector.getBitSize() - distance, result, 0, distance);
    } else {
      BitVectorAlgorithm.copy(bitVector, 0, result, result.getBitSize() - distance, distance);
      BitVectorAlgorithm.copy(bitVector, distance, result, 0, result.getBitSize() - distance);
    }

    return result;
  }

  /**
   * Performs rotation to the right of the specified bit vector by the specified shift amount.
   * The actual shift amount is calculated as {@code to} modulo {@code v.getBitSize()}. If the
   * actual shift amount equals {@code 0}, no shift is performed and the initial bit vector is
   * returned. Otherwise, a new copy of data is created and returned. If the shift amount is
   * negative, the actual shift amount is calculated as {@code v.getBitSize()} minus
   * ({@code to} modulo {@code v.getBitSize()}).
   *
   * @param bitVector Bit vector to be shifted.
   * @param to Shift amount.
   * @return Right rotation result.
   *
   * @throws IllegalArgumentException if any of the parameters is {@code null}.
   */
  public static BitVector rotr(final BitVector bitVector, final BitVector to) {
    InvariantChecks.checkNotNull(bitVector);
    InvariantChecks.checkNotNull(to);

    return rotr(bitVector, to.bigIntegerValue());
  }

  public static BitVector rotr(final BitVector bitVector, final BigInteger to) {
    InvariantChecks.checkNotNull(bitVector);
    InvariantChecks.checkNotNull(to);

    final BigInteger size = BigInteger.valueOf(bitVector.getBitSize());
    final BigInteger amount = to.mod(size);

    return doRotr(bitVector, amount.intValue());
  }

  public static BitVector rotr(final BitVector bitVector, final int to) {
    InvariantChecks.checkNotNull(bitVector);

    final int amount = to % bitVector.getBitSize();
    return doRotr(bitVector, amount);
  }

  private static BitVector doRotr(final BitVector bitVector, final int amount) {
    if (0 == amount) {
      return bitVector;
    }

    final int distance = Math.abs(amount);
    final BitVector result = BitVector.newEmpty(bitVector.getBitSize());

    if (amount > 0) {
      BitVectorAlgorithm.copy(bitVector, distance, result, 0, result.getBitSize() - distance);
      BitVectorAlgorithm.copy(bitVector, 0, result, result.getBitSize() - distance, distance);
    } else {
      BitVectorAlgorithm.copy(bitVector, result.getBitSize() - distance, result, 0, distance);
      BitVectorAlgorithm.copy(bitVector, 0, result, distance, result.getBitSize() - distance);
    }

    return result;
  }

  public static BitVector add(final BitVector lhs, final BitVector rhs) {
    return transform(lhs, rhs, new BitVectorAlgorithm.IBinaryOperation() {
      private byte carry = 0;

      @Override
      public byte run(final byte lhs, final byte rhs) {
        final int sum = (lhs & 0xFF) + (rhs & 0xFF) + (carry & 0xFF);
        carry = (byte) (sum >>> BitVector.BITS_IN_BYTE);
        return (byte) sum;
      }
    });
  }

  public static BitVector sub(final BitVector lhs, final BitVector rhs) {
    return add(lhs, neg(rhs));
  }

  public static BitVector mul(final BitVector lhs, final BitVector rhs) {
    final BigInteger result =
        lhs.bigIntegerValue(false).multiply(rhs.bigIntegerValue(false));

    return BitVector.valueOf(result, lhs.getBitSize());
  }

  public static BitVector udiv(final BitVector lhs, final BitVector rhs) {
    final BigInteger result =
        lhs.bigIntegerValue(false).divide(rhs.bigIntegerValue(false));

    return BitVector.valueOf(result, lhs.getBitSize());
  }

  public static BitVector sdiv(final BitVector lhs, final BitVector rhs) {
    final BigInteger result =
        lhs.bigIntegerValue().divide(rhs.bigIntegerValue());

    return BitVector.valueOf(result, lhs.getBitSize());
  }

  public static BitVector urem(final BitVector lhs, final BitVector rhs) {
    final BigInteger lint = lhs.bigIntegerValue(false);
    final BigInteger rint = rhs.bigIntegerValue(false);

    return BitVector.valueOf(modulo(1, lint, rint), lhs.getBitSize());
  }

  public static BitVector srem(final BitVector lhs, final BitVector rhs) {
    final BigInteger lint = lhs.bigIntegerValue();
    final BigInteger rint = rhs.bigIntegerValue();

    return BitVector.valueOf(modulo(lint.signum(), lint, rint), lhs.getBitSize());
  }

  public static BitVector smod(final BitVector lhs, final BitVector rhs) {
    final BigInteger lint = lhs.bigIntegerValue();
    final BigInteger rint = rhs.bigIntegerValue();

    return BitVector.valueOf(modulo(rint.signum(), lint, rint), lhs.getBitSize());
  }

  private static BigInteger modulo(
      final int signum,
      final BigInteger lhs,
      final BigInteger rhs) {
    final BigInteger result = lhs.abs().mod(rhs.abs());
    if (signum < 0) {
      return result.negate();
    }
    return result;
  }

  public static BitVector plus(final BitVector bitVector) {
    InvariantChecks.checkNotNull(bitVector);
    return bitVector;
  }

  public static BitVector neg(final BitVector bitVector) {
    InvariantChecks.checkNotNull(bitVector);
    // Negation algorithm: "-arg = ~arg + 1".
    return add(not(bitVector), BitVector.valueOf(1, bitVector.getBitSize()));
  }

  public static boolean ule(final BitVector lhs, final BitVector rhs) {
    checkEqualSize(lhs, rhs);
    return lhs.compareTo(rhs) <= 0;
  }

  public static boolean ult(final BitVector lhs, final BitVector rhs) {
    checkEqualSize(lhs, rhs);
    return lhs.compareTo(rhs) < 0;
  }

  public static boolean uge(final BitVector lhs, final BitVector rhs) {
    checkEqualSize(lhs, rhs);
    return lhs.compareTo(rhs) >= 0;
  }

  public static boolean ugt(final BitVector lhs, final BitVector rhs) {
    checkEqualSize(lhs, rhs);
    return lhs.compareTo(rhs) > 0;
  }

  public static boolean sle(final BitVector lhs, final BitVector rhs) {
    checkEqualSize(lhs, rhs);

    final int signBitIndex = lhs.getBitSize() - 1;

    final boolean isLeftNeg = lhs.getBit(signBitIndex);
    final boolean isRightNeg = rhs.getBit(signBitIndex);

    if (isLeftNeg != isRightNeg) {
      // If lhs is negative, it is less. Otherwise, it is greater.
      return isLeftNeg;
    }

    return lhs.compareTo(rhs) <= 0;
  }

  public static boolean slt(final BitVector lhs, final BitVector rhs) {
    checkEqualSize(lhs, rhs);

    final int signBitIndex = lhs.getBitSize() - 1;

    final boolean isLeftNeg = lhs.getBit(signBitIndex);
    final boolean isRightNeg = rhs.getBit(signBitIndex);

    if (isLeftNeg != isRightNeg) {
      // If lhs is negative, it is less. Otherwise, it is greater.
      return isLeftNeg;
    }

    return lhs.compareTo(rhs) < 0;
  }

  public static boolean sge(final BitVector lhs, final BitVector rhs) {
    checkEqualSize(lhs, rhs);

    final int signBitIndex = lhs.getBitSize() - 1;

    final boolean isLeftNeg = lhs.getBit(signBitIndex);
    final boolean isRightNeg = rhs.getBit(signBitIndex);

    if (isLeftNeg != isRightNeg) {
      // If lhs is positive, it is greater. Otherwise, it is less.
      return !isLeftNeg;
    }

    return lhs.compareTo(rhs) >= 0;
  }

  public static boolean sgt(final BitVector lhs, final BitVector rhs) {
    checkEqualSize(lhs, rhs);

    final int signBitIndex = lhs.getBitSize() - 1;

    final boolean isLeftNeg = lhs.getBit(signBitIndex);
    final boolean isRightNeg = rhs.getBit(signBitIndex);

    if (isLeftNeg != isRightNeg) {
      // If lhs is positive, it is greater. Otherwise, it is less.
      return !isLeftNeg;
    }

    return lhs.compareTo(rhs) > 0;
  }

  public static boolean eq(final BitVector lhs, final BitVector rhs) {
    checkEqualSize(lhs, rhs);
    return lhs.equals(rhs);
  }

  public static boolean neq(final BitVector lhs, final BitVector rhs) {
    checkEqualSize(lhs, rhs);
    return !lhs.equals(rhs);
  }

  public static BitVector andr(final BitVector bv) {
    InvariantChecks.checkNotNull(bv);

    if (bv.equals(not(BitVector.valueOf(0, bv.getBitSize())))) {
      return BitVector.TRUE;
    }
    return BitVector.FALSE;
  }

  public static BitVector nandr(final BitVector bv) {
    return not(andr(bv));
  }

  public static BitVector orr(final BitVector bv) {
    InvariantChecks.checkNotNull(bv);

    if (bv.equals(BitVector.valueOf(0, bv.getBitSize()))) {
      return BitVector.FALSE;
    }
    return BitVector.TRUE;
  }

  public static BitVector norr(final BitVector bv) {
    return not(orr(bv));
  }

  public static BitVector xorr(final BitVector bv) {
    InvariantChecks.checkNotNull(bv);

    int ones = 0;
    for (int i = 0; i < bv.getBitSize(); ++i) {
      if (bv.getBit(i)) {
        ++ones;
      }
    }
    return (ones % 2 == 0) ? BitVector.FALSE : BitVector.TRUE;
  }

  public static BitVector xnorr(final BitVector bv) {
    return not(xorr(bv));
  }

  private static BitVector transform(
      final BitVector lhs,
      final BitVector rhs,
      final BitVectorAlgorithm.IBinaryOperation op) {
    checkEqualSize(lhs, rhs);

    final BitVector result = BitVector.newEmpty(lhs.getBitSize());
    BitVectorAlgorithm.transform(lhs, rhs, result, op);

    return result;
  }

  private static BitVector transform(
      final BitVector bitVector,
      final BitVectorAlgorithm.IUnaryOperation op) {
    InvariantChecks.checkNotNull(bitVector);

    final BitVector result = BitVector.newEmpty(bitVector.getBitSize());
    BitVectorAlgorithm.transform(bitVector, result, op);

    return result;
  }

  private static void checkEqualSize(final BitVector lhs, final BitVector rhs) {
    InvariantChecks.checkNotNull(lhs);
    InvariantChecks.checkNotNull(rhs);

    if (lhs.getBitSize() != rhs.getBitSize()) {
      throw new IllegalArgumentException(String.format(
        "Bit vector sizes do not match: %d != %d.", lhs.getBitSize(), rhs.getBitSize()));
    }
  }
}
