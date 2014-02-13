/*
 * Copyright (c) 2014 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * BitVectorMath.java, Feb 13, 2014 4:34:41 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.data.types.bitvector;

public final class BitVectorMath
{
    private BitVectorMath() {}

    public static enum Operations
    {
        AND  { @Override public BitVector execute(BitVector lhs, BitVector rhs) { return  and(lhs, rhs); } },
        OR   { @Override public BitVector execute(BitVector lhs, BitVector rhs) { return   or(lhs, rhs); } },
        XOR  { @Override public BitVector execute(BitVector lhs, BitVector rhs) { return  xor(lhs, rhs); } },
        NOT  { @Override public BitVector execute(BitVector v)                  { return         not(v); } },
        NAND { @Override public BitVector execute(BitVector lhs, BitVector rhs) { return nand(lhs, rhs); } },
        NOR  { @Override public BitVector execute(BitVector lhs, BitVector rhs) { return  nor(lhs, rhs); } },
        XNOR { @Override public BitVector execute(BitVector lhs, BitVector rhs) { return xnor(lhs, rhs); } };

        // IMPORTANT: must be overridden if supported by a specific operation.
        public BitVector execute(BitVector v)
        {
            throw new UnsupportedOperationException(
               String.format("Unary %s operation is not supported", name()));
        }

        // IMPORTANT: must be overridden if supported by a specific operation.
        public BitVector execute(BitVector lhs, BitVector rhs)
        {
            throw new UnsupportedOperationException(
               String.format("Binary %s operation is not supported", name()));
        }
    }

    public static BitVector and(BitVector lhs, BitVector rhs)
    {
        return transform(lhs, rhs, BitVectorAlgorithm.BinaryOperation.AND);
    }

    public static BitVector or(BitVector lhs, BitVector rhs)
    {
        return transform(lhs, rhs, BitVectorAlgorithm.BinaryOperation.OR);
    }

    public static BitVector xor(BitVector lhs, BitVector rhs)
    {
        return transform(lhs, rhs, BitVectorAlgorithm.BinaryOperation.XOR);
    }

    public static BitVector not(BitVector v)
    {
        return transform(v, BitVectorAlgorithm.UnaryOperation.NOT);
    }

    public static BitVector nand(BitVector lhs, BitVector rhs)
    {
        return not(and(lhs, rhs));
    }

    public static BitVector nor(BitVector lhs, BitVector rhs)
    {
        return not(or(lhs, rhs));
    }

    public static BitVector xnor(BitVector lhs, BitVector rhs)
    {
        return not(xor(lhs, rhs));
    }

    private static BitVector transform(BitVector lhs, BitVector rhs, BitVectorAlgorithm.IBinaryOperation op)
    {
        checkNotNull(lhs);
        checkNotNull(rhs);
        checkEqualSize(lhs, rhs);

        final BitVector result = BitVector.newEmpty(lhs.getBitSize());
        BitVectorAlgorithm.transform(lhs, rhs, result, op);

        return result;
    }

    private static BitVector transform(BitVector v, BitVectorAlgorithm.IUnaryOperation op)
    {
        checkNotNull(v);

        final BitVector result = BitVector.newEmpty(v.getBitSize());
        BitVectorAlgorithm.transform(v, result, op);

        return result;
    }

    private static void checkNotNull(Object o)
    {
        if (null == o)
            throw new NullPointerException();
    }

    private static void checkEqualSize(BitVector lhs, BitVector rhs)
    {
        if (lhs.getBitSize() != rhs.getBitSize())
            throw new IllegalArgumentException(
                String.format("Bit vector sizes do not match: %d != %d.", lhs.getBitSize(), rhs.getBitSize()));
    }
}
