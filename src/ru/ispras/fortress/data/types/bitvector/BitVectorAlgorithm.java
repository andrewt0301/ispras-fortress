/*
 * Copyright (c) 2012 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * BitVectorAlgorithm.java, Oct 17, 2012 4:44:59 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.data.types.bitvector;

public final class BitVectorAlgorithm
{
    private BitVectorAlgorithm() {}

    public static interface IUnaryOperation
    {
        public byte run(byte v);
    }

    public static interface IBinaryOperation
    {
        public byte run(byte lhs, byte rhs);
    }

    public static interface IOperation
    {
        public byte run();
    }

    public static interface IAction
    {
        public void run(byte v);
    }

    public static void fill(BitVector dest, byte value)
    {
        notNullCheck(dest, "dest");

        for (int index = 0; index < dest.getByteSize(); ++index)
        {
            dest.setByte(index, value);
        }
    }

    public static void generate(BitVector dest, IOperation op)
    {
        notNullCheck(dest, "dest");

        for (int index = 0; index < dest.getByteSize(); ++index)
        {
            dest.setByte(index, op.run());
        }        
    }

    public static void copy(BitVector src, BitVector dest)
    {
        notNullCheck(src,   "src");
        notNullCheck(dest, "dest");

        if (src == dest)
            return;

        for (int index = 0; index < dest.getByteSize(); ++index)
        {
           dest.setByte(index, index < src.getByteSize() ? src.getByte(index) : (byte) 0);
        }
    }
    
    public static void copy(BitVector src, int srcPos, BitVector dest, int destPos, int bitSize)
    {
        notNullCheck(src,   "src");
        notNullCheck(dest, "dest");

        if ((src == dest) && (srcPos == destPos))
            return;

        final BitVector  srcMapping = BitVector.newMapping(src,   srcPos, bitSize);
        final BitVector destMapping = BitVector.newMapping(dest, destPos, bitSize);

        copy(srcMapping, destMapping);
    }

    public static void for_each(BitVector src, IAction op)
    {
        notNullCheck(src, "src");
        notNullCheck(op,   "op");

        for (int index = 0; index < src.getByteSize(); ++index)
        {
            op.run(src.getByte(index));
        }
    }

    public static void for_each_reverse(BitVector src, IAction op)
    {
        notNullCheck(src, "src");
        notNullCheck(op,   "op");

        for (int index = src.getByteSize() - 1; index >= 0; --index)
        {
            op.run(src.getByte(index));
        }
    }

    public static int mismatch_reverse(BitVector src1, BitVector src2)
    {
        notNullCheck(src1, "src1");
        notNullCheck(src2, "src2");

        equalSizeCheck(src1.getBitSize(), src1.getBitSize());

        if (src1 == src2)
            return -1;

        for (int index = src1.getByteSize() - 1; index >= 0; --index)
        {
            if (src1.getByte(index) != src2.getByte(index))
                return index;
        }

        return -1;
    }

    public static void transform(BitVector src, BitVector dest, IUnaryOperation op)
    {
        notNullCheck(src,   "src");
        notNullCheck(dest, "dest");
        notNullCheck(op,     "op");

        equalSizeCheck(src.getBitSize(), dest.getBitSize());

        for (int index = 0; index < dest.getByteSize(); ++index)
        {
            dest.setByte(index, op.run(src.getByte(index)));
        }
    }

    public static void transform(BitVector src1, BitVector src2, BitVector dest, IBinaryOperation op)
    {
        notNullCheck(src1, "src1");
        notNullCheck(src2, "src2");
        notNullCheck(dest, "dest");
        notNullCheck(op,     "op");

        equalSizeCheck(src1.getBitSize(), dest.getBitSize());
        equalSizeCheck(src2.getBitSize(), dest.getBitSize());

        for (int index = 0; index < dest.getByteSize(); ++index)
        {
            dest.setByte(index, op.run(src1.getByte(index), src2.getByte(index)));
        }
    }

    private static void notNullCheck(Object o, String name)
    {
        if (null == o)
            throw new NullPointerException("null == " + name);
    }

    private static void equalSizeCheck(int size1, int size2)
    {
        if (size1 != size2)
            throw new IllegalArgumentException("Invariant is violated: " + size1 + " != " + size2);
    }
}
