/*
 * Copyright (c) 2012 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * BitVectorStore.java, Oct 11, 2012 12:46:54 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.data.types.bitvector;

/**
 * The BitVectorStore class represents a data array that stores binary data of a bit vector.
 * Data can be accessed by bytes. If the number of bits is not multiple of 8 (number of bits in a byte)
 * the highest byte is truncated (its highest bits are excluded).  
 *
 * <pre>
 * Example:
 *
 * Data representation for a 29-bit long data array. The highest 3 bits are "cut off" by a bit mask.
 * 
 * Byte:
 * 4        3        2        1        0
 *
 * Bit:
 * 32  29!  24       16       8        0
 * _____________________________________
 * |   !    |        |        |        |
 * |%%%!    |        |        |        |
 * |%%%!    |        |        |        |
 * |___!____|________|________|________|
 *
 * Bit size:       29
 * Byte size:      4
 * High byte mask: 00011111 (binary)
 * </pre>
 *
 * @author Andrei Tatarnikov
 */

final class BitVectorStore extends BitVector 
{  
    private final byte[] dataBytes; // Array that stores binary data. 
    private final int      bitSize; // Number of used bits.

    /**
     * Allocates a bit vector. 
     *
     * @param bitSize Data size in bits.
     */

    public BitVectorStore(int bitSize)
    {
        sizeCheck(bitSize);

        final int byteSize = bitSize / BITS_IN_BYTE + (0 == (bitSize % BITS_IN_BYTE) ? 0 : 1);

        this.bitSize   = bitSize;
        this.dataBytes = new byte[byteSize];

        reset();
    }

    /**
     * Creates a copy of existing an bit vector.
     *
     * @param src An existing bit vector to be copied.
     */

    public BitVectorStore(BitVector src)
    {
        if (null == src)
            throw new NullPointerException();

        this.dataBytes = new byte[src.getByteSize()];
        this.bitSize   = src.getBitSize();

        assign(src);
    }

    /**
     * {@inheritDoc}
     */

    @Override
    public int getBitSize()
    {
        return bitSize;
    }

    /**
     * {@inheritDoc}
     */

    @Override 
    public int getByteSize()
    {
        return dataBytes.length;
    }

    /**
     * {@inheritDoc}
     */

    @Override 
    public byte getByte(int index)
    {
        rangeCheck(index, getByteSize());

        return (byte)(dataBytes[index] & getByteBitMask(index));
    }

    /**
     * {@inheritDoc}
     */

    @Override 
    public void setByte(int index, byte value)
    {
        rangeCheck(index, getByteSize());

        final byte mask = getByteBitMask(index);
        final byte old  = dataBytes[index];

        // Bits beyond the range <bitCount-1..0> are preserved.
        dataBytes[index] = (byte)((old & ~mask) | (value & mask));

        // To make sure that bits beyond the bound have not been changed.
        assert ((byte)(old & ~mask)) == ((byte)(dataBytes[index] & ~mask));
    }
}
