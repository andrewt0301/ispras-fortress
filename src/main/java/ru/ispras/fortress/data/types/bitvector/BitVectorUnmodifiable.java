/*
 * Copyright (c) 2013 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * BitVectorUnmodifiable.java, Nov 6, 2013 10:28:57 AM Andrei Tatarnikov
 */

package ru.ispras.fortress.data.types.bitvector;

/**
 * The BitVectorUnmodifiable class is a wrapper around a BitVector object
 * that forbids modification of data stored in the bit vector.
 * 
 * @author Andrei Tatarnikov
 */

final class BitVectorUnmodifiable extends BitVector
{
    private final BitVector bitVector;

    public BitVectorUnmodifiable(BitVector bitVector)
    {
        if (null == bitVector)
            throw new NullPointerException();

        this.bitVector = bitVector;
    }

    @Override
    public int getBitSize()
    {
        return bitVector.getBitSize();
    }

    @Override
    public int getByteSize()
    {
        return bitVector.getByteSize();
    }

    @Override
    public byte getByte(int index)
    {
        return bitVector.getByte(index);
    }

    @Override
    public void setByte(int index, byte value)
    {
        throw new UnsupportedOperationException();
    }
}
