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

  public static interface IUnaryOperation {
    public byte run(byte v);
  }

  public static interface IBinaryOperation {
    public byte run(byte lhs, byte rhs);
  }

  public static interface IOperation {
    public byte run();
  }

  public static interface IAction {
    public void run(byte v);
  }

  public static interface IBinaryPredicate {
    public boolean test(byte lhs, byte rhs);
  }

  public static enum UnaryOperation implements IUnaryOperation {
    NOT {
      @Override
      public byte run(byte v) {
        return (byte) ~v;
      }
    };
  }

  public static enum BinaryOperation implements IBinaryOperation {
    AND {
      @Override
      public byte run(byte lhs, byte rhs) {
        return (byte) (lhs & rhs);
      }
    },
    OR {
      @Override
      public byte run(byte lhs, byte rhs) {
        return (byte) (lhs | rhs);
      }
    },
    XOR {
      @Override
      public byte run(byte lhs, byte rhs) {
        return (byte) (lhs ^ rhs);
      }
    };
  }

  // All byte comparisons are unsigned.
  public static enum BinaryPredicate implements IBinaryPredicate {
    LE {
      @Override
      public boolean test(byte lhs, byte rhs) {
        return (lhs & 0xFF) <= (rhs & 0xFF);
      }
    },
    LT {
      @Override
      public boolean test(byte lhs, byte rhs) {
        return (lhs & 0xFF) < (rhs & 0xFF);
      }
    },
    GE {
      @Override
      public boolean test(byte lhs, byte rhs) {
        return (lhs & 0xFF) >= (rhs & 0xFF);
      }
    },
    GT {
      @Override
      public boolean test(byte lhs, byte rhs) {
        return (lhs & 0xFF) > (rhs & 0xFF);
      }
    };
  }

  public static void fill(BitVector dest, byte value) {
    checkNotNull(dest, "dest");

    for (int index = 0; index < dest.getByteSize(); ++index) {
      dest.setByte(index, value);
    }
  }

  public static void generate(BitVector dest, IOperation op) {
    checkNotNull(dest, "dest");

    for (int index = 0; index < dest.getByteSize(); ++index) {
      dest.setByte(index, op.run());
    }
  }

  public static void copy(BitVector src, BitVector dest) {
    checkNotNull(src, "src");
    checkNotNull(dest, "dest");

    if (src == dest) {
      return;
    }

    for (int index = 0; index < dest.getByteSize(); ++index) {
      dest.setByte(index, index < src.getByteSize() ? src.getByte(index) : (byte) 0);
    }
  }

  public static void copy(BitVector src, int srcPos, BitVector dest, int destPos, int bitSize) {
    checkNotNull(src, "src");
    checkNotNull(dest, "dest");

    if ((src == dest) && (srcPos == destPos)) {
      return;
    }

    final BitVector srcMapping = BitVector.newMapping(src, srcPos, bitSize);
    final BitVector destMapping = BitVector.newMapping(dest, destPos, bitSize);

    copy(srcMapping, destMapping);
  }

  public static void for_each(BitVector src, IAction op) {
    checkNotNull(src, "src");
    checkNotNull(op, "op");

    for (int index = 0; index < src.getByteSize(); ++index) {
      op.run(src.getByte(index));
    }
  }

  public static void for_each_reverse(BitVector src, IAction op) {
    checkNotNull(src, "src");
    checkNotNull(op, "op");

    for (int index = src.getByteSize() - 1; index >= 0; --index) {
      op.run(src.getByte(index));
    }
  }

  public static int mismatch(BitVector src1, BitVector src2) {
    checkNotNull(src1, "src1");
    checkNotNull(src2, "src2");

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

  public static int mismatch(BitVector src1, BitVector src2, IBinaryPredicate op) {
    checkNotNull(src1, "src1");
    checkNotNull(src2, "src2");
    checkNotNull(op, "op");

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

  public static int mismatch_reverse(BitVector src1, BitVector src2) {
    checkNotNull(src1, "src1");
    checkNotNull(src2, "src2");

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

  public static int mismatch_reverse(BitVector src1, BitVector src2, IBinaryPredicate op) {
    checkNotNull(src1, "src1");
    checkNotNull(src2, "src2");
    checkNotNull(op, "op");

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

  public static void transform(BitVector src, BitVector dest, IUnaryOperation op) {
    checkNotNull(src, "src");
    checkNotNull(dest, "dest");
    checkNotNull(op, "op");

    checkEqualSize(src.getBitSize(), dest.getBitSize());

    for (int index = 0; index < dest.getByteSize(); ++index) {
      dest.setByte(index, op.run(src.getByte(index)));
    }
  }

  public static void transform(BitVector src1, BitVector src2, BitVector dest, IBinaryOperation op) {
    checkNotNull(src1, "src1");
    checkNotNull(src2, "src2");
    checkNotNull(dest, "dest");
    checkNotNull(op, "op");

    checkEqualSize(src1.getBitSize(), dest.getBitSize());
    checkEqualSize(src2.getBitSize(), dest.getBitSize());

    for (int index = 0; index < dest.getByteSize(); ++index) {
      dest.setByte(index, op.run(src1.getByte(index), src2.getByte(index)));
    }
  }

  private static void checkEqualSize(int size1, int size2) {
    if (size1 != size2) {
      throw new IllegalArgumentException("Invariant is violated: " + size1 + " != " + size2);
    }
  }
}
