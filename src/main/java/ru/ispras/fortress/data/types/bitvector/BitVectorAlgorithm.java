/*
 * Copyright 2012-2015 ISP RAS (http://www.ispras.ru)
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

public final class BitVectorAlgorithm {
  private BitVectorAlgorithm() {}

  public interface IUnaryOperation {
    byte run(byte v);
  }

  public interface IBinaryOperation {
    byte run(final byte lhs, final byte rhs);
  }

  public interface IOperation {
    byte run();
  }

  public interface IAction {
    void run(byte v);
  }

  public interface IBinaryPredicate {
    boolean test(final byte lhs, final byte rhs);
  }

  public static enum UnaryOperation implements IUnaryOperation {
    NOT {
      @Override
      public byte run(final byte v) {
        return (byte) ~v;
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

  public static void fill(final BitVector dest, final byte value) {
    checkNotNull(dest);

    for (int index = 0; index < dest.getByteSize(); ++index) {
      dest.setByte(index, value);
    }
  }

  public static void generate(final BitVector dest, final IOperation op) {
    checkNotNull(dest);

    for (int index = 0; index < dest.getByteSize(); ++index) {
      dest.setByte(index, op.run());
    }
  }

  public static void copy(final BitVector src, final BitVector dest) {
    checkNotNull(src);
    checkNotNull(dest);

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
    checkNotNull(src);
    checkNotNull(dest);

    if (src == dest && srcPos == destPos) {
      return;
    }

    final BitVector srcMapping = BitVector.newMapping(src, srcPos, bitSize);
    final BitVector destMapping = BitVector.newMapping(dest, destPos, bitSize);

    copy(srcMapping, destMapping);
  }

  public static void forEach(final BitVector src, final IAction op) {
    checkNotNull(src);
    checkNotNull(op);

    for (int index = 0; index < src.getByteSize(); ++index) {
      op.run(src.getByte(index));
    }
  }

  public static void forEachReverse(final BitVector src, final IAction op) {
    checkNotNull(src);
    checkNotNull(op);

    for (int index = src.getByteSize() - 1; index >= 0; --index) {
      op.run(src.getByte(index));
    }
  }

  public static int mismatch(final BitVector src1, final BitVector src2) {
    checkNotNull(src1);
    checkNotNull(src2);

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
    checkNotNull(src1);
    checkNotNull(src2);
    checkNotNull(op);

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
    checkNotNull(src1);
    checkNotNull(src2);

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
    checkNotNull(src1);
    checkNotNull(src2);
    checkNotNull(op);

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
    checkNotNull(src);
    checkNotNull(dest);
    checkNotNull(op);

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
    checkNotNull(src1);
    checkNotNull(src2);
    checkNotNull(dest);
    checkNotNull(op);

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
