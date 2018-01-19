/*
 * Copyright 2012-2018 ISP RAS (http://www.ispras.ru)
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

import ru.ispras.fortress.util.InvariantChecks;

public final class BitVectorAlgorithm {
  private BitVectorAlgorithm() {}

  public interface IUnaryOperation {
    byte run(final byte byteValue);
  }

  public interface IBinaryOperation {
    byte run(final byte lhs, final byte rhs);
  }

  public interface IOperation {
    byte run();
  }

  public interface IAction {
    void run(final byte byteValue);
  }

  public interface IBinaryPredicate {
    boolean test(final byte lhs, final byte rhs);
  }

  public static enum UnaryOperation implements IUnaryOperation {
    NOT {
      @Override
      public byte run(final byte byteValue) {
        return (byte) ~byteValue;
      }
    };
  }

  public static enum BinaryOperation implements IBinaryOperation {
    AND {
      @Override
      public byte run(final byte lhs, final byte rhs) {
        return (byte) (lhs & rhs);
      }
    },
    OR {
      @Override
      public byte run(final byte lhs, final byte rhs) {
        return (byte) (lhs | rhs);
      }
    },
    XOR {
      @Override
      public byte run(final byte lhs, final byte rhs) {
        return (byte) (lhs ^ rhs);
      }
    };
  }

  // All byte comparisons are unsigned.
  public static enum BinaryPredicate implements IBinaryPredicate {
    LE {
      @Override
      public boolean test(final byte lhs, final byte rhs) {
        return (lhs & 0xFF) <= (rhs & 0xFF);
      }
    },
    LT {
      @Override
      public boolean test(final byte lhs, final byte rhs) {
        return (lhs & 0xFF) < (rhs & 0xFF);
      }
    },
    GE {
      @Override
      public boolean test(final byte lhs, final byte rhs) {
        return (lhs & 0xFF) >= (rhs & 0xFF);
      }
    },
    GT {
      @Override
      public boolean test(final byte lhs, final byte rhs) {
        return (lhs & 0xFF) > (rhs & 0xFF);
      }
    };
  }

  /**
   * Fills the specified bit vector with the specified byte value.
   *
   * @param dest Bit vector to be filled.
   * @param value Byte value.
   *
   * @throws IllegalArgumentException if the {@code dest} argument is {@code null}.
   */
  public static void fill(final BitVector dest, final byte value) {
    InvariantChecks.checkNotNull(dest);

    for (int index = 0; index < dest.getByteSize(); ++index) {
      dest.setByte(index, value);
    }
  }

  /**
   * Fills the specified bit vector with the byte values produced by the specified
   * {@link IOperation} object.
   *
   * @param dest Bit vector to be filled.
   * @param op Operation object that produces byte values.
   *
   * @throws IllegalArgumentException if any of the arguments is {@code null}.
   */
  public static void generate(final BitVector dest, final IOperation op) {
    InvariantChecks.checkNotNull(dest);
    InvariantChecks.checkNotNull(op);

    for (int index = 0; index < dest.getByteSize(); ++index) {
      dest.setByte(index, op.run());
    }
  }

  /**
   * Copies the contents of one bit vector into another bit vector. The source is shorter
   * than the destination, the high bytes of the destination are filled with zeros.
   *
   * @param src Source bit vector.
   * @param dest Destination bit vector.
   *
   * @throws IllegalArgumentException if any of the arguments is {@code null}.
   */
  public static void copy(final BitVector src, final BitVector dest) {
    InvariantChecks.checkNotNull(src);
    InvariantChecks.checkNotNull(dest);

    if (src == dest) {
      return;
    }

    for (int index = 0; index < dest.getByteSize(); ++index) {
      dest.setByte(index, index < src.getByteSize() ? src.getByte(index) : (byte) 0);
    }
  }

  public static void copy(
      final BitVector src,
      final int srcPos,
      final BitVector dest,
      final int destPos,
      final int bitSize) {
    InvariantChecks.checkNotNull(src);
    InvariantChecks.checkNotNull(dest);

    if (src == dest && srcPos == destPos) {
      return;
    }

    final BitVector srcMapping = BitVector.newMapping(src, srcPos, bitSize);
    final BitVector destMapping = BitVector.newMapping(dest, destPos, bitSize);

    copy(srcMapping, destMapping);
  }

  public static void forEach(final BitVector src, final IAction op) {
    InvariantChecks.checkNotNull(src);
    InvariantChecks.checkNotNull(op);

    for (int index = 0; index < src.getByteSize(); ++index) {
      op.run(src.getByte(index));
    }
  }

  public static void forEachReverse(final BitVector src, final IAction op) {
    InvariantChecks.checkNotNull(src);
    InvariantChecks.checkNotNull(op);

    for (int index = src.getByteSize() - 1; index >= 0; --index) {
      op.run(src.getByte(index));
    }
  }

  public static int mismatch(final BitVector src1, final BitVector src2) {
    InvariantChecks.checkNotNull(src1);
    InvariantChecks.checkNotNull(src2);

    checkEqualSize(src1.getBitSize(), src2.getBitSize());

    if (src1 == src2) {
      return -1;
    }

    for (int index = 0; index < src1.getByteSize(); ++index) {
      if (src1.getByte(index) != src2.getByte(index)) {
        return index;
      }
    }

    return -1;
  }

  public static int mismatch(
      final BitVector src1,
      final BitVector src2,
      final IBinaryPredicate op) {
    InvariantChecks.checkNotNull(src1);
    InvariantChecks.checkNotNull(src2);
    InvariantChecks.checkNotNull(op);

    checkEqualSize(src1.getBitSize(), src2.getBitSize());

    if (src1 == src2) {
      return -1;
    }

    for (int index = 0; index < src1.getByteSize(); ++index) {
      if (!op.test(src1.getByte(index), src2.getByte(index))) {
        return index;
      }
    }

    return -1;
  }

  public static int mismatchReverse(final BitVector src1, final BitVector src2) {
    InvariantChecks.checkNotNull(src1);
    InvariantChecks.checkNotNull(src2);

    checkEqualSize(src1.getBitSize(), src2.getBitSize());

    if (src1 == src2) {
      return -1;
    }

    for (int index = src1.getByteSize() - 1; index >= 0; --index) {
      if (src1.getByte(index) != src2.getByte(index)) {
        return index;
      }
    }

    return -1;
  }

  public static int mismatchReverse(
      final BitVector src1, 
      final BitVector src2,
      final IBinaryPredicate op) {
    InvariantChecks.checkNotNull(src1);
    InvariantChecks.checkNotNull(src2);
    InvariantChecks.checkNotNull(op);

    checkEqualSize(src1.getBitSize(), src2.getBitSize());

    if (src1 == src2) {
      return -1;
    }

    for (int index = src1.getByteSize() - 1; index >= 0; --index) {
      if (!op.test(src1.getByte(index), src2.getByte(index))) {
        return index;
      }
    }

    return -1;
  }

  public static void transform(
      final BitVector src,
      final BitVector dest,
      final IUnaryOperation op) {
    InvariantChecks.checkNotNull(src);
    InvariantChecks.checkNotNull(dest);
    InvariantChecks.checkNotNull(op);

    checkEqualSize(src.getBitSize(), dest.getBitSize());

    for (int index = 0; index < dest.getByteSize(); ++index) {
      dest.setByte(index, op.run(src.getByte(index)));
    }
  }

  public static void transform(
      final BitVector src1,
      final BitVector src2,
      final BitVector dest,
      final IBinaryOperation op) {
    InvariantChecks.checkNotNull(src1);
    InvariantChecks.checkNotNull(src2);
    InvariantChecks.checkNotNull(dest);
    InvariantChecks.checkNotNull(op);

    checkEqualSize(src1.getBitSize(), dest.getBitSize());
    checkEqualSize(src2.getBitSize(), dest.getBitSize());

    for (int index = 0; index < dest.getByteSize(); ++index) {
      dest.setByte(index, op.run(src1.getByte(index), src2.getByte(index)));
    }
  }

  private static void checkEqualSize(final int size1, final int size2) {
    if (size1 != size2) {
      throw new IllegalArgumentException("Invariant is violated: " + size1 + " != " + size2);
    }
  }
}
