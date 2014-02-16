/*
 * Copyright (c) 2012 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * BitVectorMapping.java, Oct 11, 2012 12:49:59 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.data.types.bitvector;

/**
 * The BitVectorMapping class provides the possibility to map a bit vector to
 * another bit vector. Mapping can start at an arbitrary position and can have
 * an arbitrary length (bounded by the size of the source bit vector).
 *
 * <pre>
 * The scheme below demonstrates how the class works:
 *
 * Source data array (a 29-bit vector) and a 10-bit mapping that starts from the 3th bit:
 *
 * Real data:
 *
 * Bits:
 * 31 29! 24       16 13 12   8 7   3   0
 * ______________________________________
 * |   !    |        |   |     |     |   |
 * |%%%!    |        |HHH|XXXXX|XXXXX|LLL|
 * |%%%!    |        |HHH|XXXXX|XXXXX|LLL|
 * |___!____|________|___|_____|_____|___|
 *
 * Mapped view:
 *
 * Bits: 
 * 15   10  8 7       0
 * ___________________
 * |      |  |        |
 * |%%%%%%|XX|XXXXXXXX|
 * |%%%%%%|XX|XXXXXXXX|
 * |______|__|________|
 *
 * (%) - excluded area
 * (X) - mapped area
 * (H) - high byte mask area. The mask excludes the marked bits (mask bits are set to zero). 
 * (L) - low byte mask area. The mask excludes the marked bits (mask bits are set to zero).
 *
 * When we work with data via a mapping, the methods of the BitVectorMapping class split bytes into
 * parts and perform the needed bit operations to align the data in a proper way.  
 * </pre>
 *
 * @author Andrei Tatarnikov
 */

final class BitVectorMapping extends BitVector
{
    private final BitVector source;
    private final int  beginBitPos;
    private final int      bitSize;

    /**
     * Creates a mapping for the specified bit vector. 
     *  
     * @param src The source bit vector.
     * @param beginBitPos The starting position of the mapping.
     * @param bitSize The length of the mapping in bits.
     */

    public BitVectorMapping(BitVector src, int beginBitPos, int bitSize)
    {
        if (null == src)
            throw new NullPointerException();

        sizeCheck(bitSize);
        rangeCheck(beginBitPos, src.getBitSize());
        rangeCheckInclusive(beginBitPos + bitSize, src.getBitSize());

        this.source      = src;
        this.beginBitPos = beginBitPos;
        this.bitSize     = bitSize;
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
        return bitSize / BITS_IN_BYTE + ((0 == bitSize % BITS_IN_BYTE) ? 0 : 1);
    }

    /**
     * {@inheritDoc}
     */

    @Override
    public byte getByte(int index)
    {
        // TODO: Refactoring is needed. The implementation is not perfectly clear
        // and may contain subtle bugs.

        rangeCheck(index, getByteSize());

        final int byteIndex = getByteIndex(index);
        rangeCheck(byteIndex, source.getByteSize());

        final int excludedLowBits = getExcludedLowBitCount();
        
        // If there are no lower bits excluded from a byte this means that data
        // is aligned by bytes and no data transformation is needed. If there is an incomplete
        // high byte, we just apply a bit mask for the specified byte.

        if (0 == excludedLowBits)
            return (byte)(source.getByte(byteIndex) & getByteBitMask(index));

        // Takes needed bits (the higher part) of the low byte (specified by byteIndex) and
        // shifts them to the beginning of the byte (towards the least significant part).

        final byte lowByte =
            (byte)((source.getByte(byteIndex) & 0xFF) >>> excludedLowBits);

        // If there is no bytes left in the data array, we don't go further.
        if (byteIndex == getEndByteIndex())
            return (byte)(lowByte & getByteBitMask(index));

        // Takes the needed bits (the lower part) of the high byte (following after the low byte)
        // and shifts them to the end of the byte (towards the most significant part).

        final byte highByte =
            (byte)(source.getByte(byteIndex + 1) << (BITS_IN_BYTE - excludedLowBits));

        // Unites the low and high parts and cuts bits to be excluded with help of a mask
        // (in case if we are addressing an incomplete high byte).

        return (byte)((highByte | lowByte) & getByteBitMask(index));
    }

    /**
     * {@inheritDoc}
     */

    @Override
    public void setByte(int index, byte value)
    {
        // TODO: Refactoring is needed. The implementation is not perfectly clear
        // and may contain subtle bugs.

        rangeCheck(index, getByteSize());

        final int byteIndex = getByteIndex(index);
        rangeCheck(byteIndex, source.getByteSize());

        final int excludedLowBits  = getExcludedLowBitCount();
        final int excludedHighBits = getExcludedHighBitCount();

        final int endByteIndex = getEndByteIndex();

        final byte  lowByteMask = (0 == excludedLowBits)  ? 0 : (byte)(0xFF << excludedLowBits);
        final byte highByteMask = (0 == excludedHighBits) ? 0 : (byte)(0xFF >>> excludedHighBits);
        
        final boolean isHighByteMaskApplied = (byteIndex == endByteIndex) && (0 != excludedHighBits);

        // If no lower bites are excluded this means that data is aligned by bytes
        // (start position is multiple of 8) and no byte split is needed.

        if (0 == excludedLowBits)
        {
            // If this is the highest byte of the mapping, it might be incomplete. In this case,
            // we need to preserve the excluded part of the target byte from overwriting.  

            final byte prevValue = (byte)(isHighByteMaskApplied ? (source.getByte(byteIndex) & ~highByteMask) : 0);

            // Excludes the redundant bits from the value and unites it with the initial value
            // part to be preserved.

            source.setByte(byteIndex, (byte)(prevValue | (value & getByteBitMask(index))) );
            return;
        }

        // Forms the mask to preserve previous values of bits that are not affected by 
        // the modification (in incomplete low and high bytes).

        final byte prevValueMask =
            (byte)(isHighByteMaskApplied ? (~lowByteMask | ~highByteMask) & 0xFF : ~lowByteMask & 0xFF);
        
        // Moves the low part of the specified byte to the high border of the byte
        // and unites the result with the old part of the target byte that should be preserved.
        // Also, we reset all redundant bits that go beyond the border of the high incomplete byte. 

        final byte    prevValue = (byte)(source.getByte(byteIndex) & prevValueMask);
        final byte alignedValue = (byte)((value << excludedLowBits) & 0xFF);

        final byte lowByte =
            (byte)((alignedValue & (isHighByteMaskApplied ? highByteMask : 0xFF)) | prevValue);

        source.setByte(byteIndex, lowByte);

        // If there is not bytes left in the data array
        // (the highest is the current), we don't go further.

        if (byteIndex == endByteIndex)
            return;

        // Moves the high part of the parameter byte to the low border (beginning) of the byte and unites
        // it with the high part of the target byte that we want to preserve. Also, in case when the high
        // part of the target byte is limited with the high border of the mask, we reset all excluded bits
        // with a high byte mask.

        final byte     prevHighValue = (byte) (source.getByte(byteIndex+1) & lowByteMask);
        final byte allignedHighValue = (byte)((value & 0xFF) >>> (BITS_IN_BYTE - excludedLowBits));

        final byte highByte = (byte)
        (
            (allignedHighValue & ((byteIndex+1 == endByteIndex) & (0 != excludedHighBits) ? highByteMask : 0xFF))
            |
            prevHighValue
        );
        
        source.setByte(byteIndex + 1, highByte);
    }

    private int getByteIndex(int index)
    {
        return beginBitPos / BITS_IN_BYTE + index;
    }

    private int getEndByteIndex()
    {
        return (beginBitPos + bitSize - 1) / BITS_IN_BYTE; // Highest bit position / bits in byte
    }

    private int getExcludedLowBitCount()
    {
        return beginBitPos % BITS_IN_BYTE;
    }

    private int getExcludedHighBitCount()
    {
        return (BITS_IN_BYTE - (beginBitPos + bitSize) % BITS_IN_BYTE) % BITS_IN_BYTE;    
    }
}
