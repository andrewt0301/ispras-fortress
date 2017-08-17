/*
 * Copyright 2012-2017 ISP RAS (http://www.ispras.ru)
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

/**
 * The {@link BitVectorMapping} class provides the possibility to map a bit vector to another bit
 * vector. Mapping can start at an arbitrary position and can have an arbitrary length (bounded by
 * the size of the source bit vector).
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
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
final class BitVectorMapping extends BitVector {
  private final BitVector source;
  private final int bitSize;
  private final int byteSize;
  private final int byteOffset;
  private final int endByteIndex;
  private final int excludedLowBitCount;

  /**
   * Creates a mapping for the specified bit vector.
   * 
   * @param src The source bit vector.
   * @param beginBitPos The starting position of the mapping.
   * @param bitSize The length of the mapping in bits.
   */
  public BitVectorMapping(
      final BitVector src,
      final int beginBitPos,
      final int bitSize) {
    InvariantChecks.checkNotNull(src);
    InvariantChecks.checkGreaterThanZero(bitSize);

    InvariantChecks.checkBounds(beginBitPos, src.getBitSize());
    InvariantChecks.checkBoundsInclusive(beginBitPos + bitSize, src.getBitSize());

    this.source = src;
    this.bitSize = bitSize;
    this.byteSize = bitSize / BITS_IN_BYTE + ((0 == bitSize % BITS_IN_BYTE) ? 0 : 1);
    this.byteOffset =  beginBitPos / BITS_IN_BYTE;
    this.endByteIndex = (beginBitPos + bitSize - 1) / BITS_IN_BYTE;
    this.excludedLowBitCount = beginBitPos % BITS_IN_BYTE;
  }

  /**
   * {@inheritDoc}
   */
  @Override
  public int getBitSize() {
    return bitSize;
  }

  /**
   * {@inheritDoc}
   */
  @Override
  public int getByteSize() {
    return byteSize;
  }

  /**
   * {@inheritDoc}
   */
  @Override
  public byte getByte(final int index) {
    InvariantChecks.checkBounds(index, getByteSize());

    final int byteIndex = byteOffset + index;
    final byte byteBitMask = getByteBitMask(index);

    // Takes needed bits (the higher part) of the low byte (specified by byteIndex) and
    // shifts them to the beginning of the byte (towards the least significant part).
    final byte lowByte =
        (byte) ((source.getByte(byteIndex) & 0xFF) >>> excludedLowBitCount);

    // If there is no bytes left in the data array, we don't go further.
    if (byteIndex == endByteIndex) {
      return (byte) (lowByte & byteBitMask);
    }

    // Takes the needed bits (the lower part) of the high byte (following after the low byte)
    // and shifts them to the end of the byte (towards the most significant part).
    final byte highByte =
        (byte) (source.getByte(byteIndex + 1) << (BITS_IN_BYTE - excludedLowBitCount));

    // Unites the low and high parts and cuts bits to be excluded with help of a mask
    // (in case if we are addressing an incomplete high byte).
    return (byte) ((highByte | lowByte) & byteBitMask);
  }

  /**
   * {@inheritDoc}
   */
  @Override
  public void setByte(final int index, final byte value) {
    InvariantChecks.checkBounds(index, getByteSize());

    final int byteIndex = byteOffset + index;
    final byte byteBitMask = getByteBitMask(index);

    // Forms the mask to preserve previous values of bits that are not affected by
    // the modification (in incomplete low and high bytes).
    final byte lowByteMask = (byte) (byteBitMask << excludedLowBitCount);

    // Gets the low byte value to be preserved.
    final byte prevLowByte = (byte) (source.getByte(byteIndex) & ~lowByteMask);

    // Moves the low part of the specified byte to the high border of the byte
    // and unites the result with the old part of the target byte that should be preserved.
    // Also, we reset all redundant bits that go beyond the border of the high incomplete byte.
    final byte lowByte = (byte) (((value << excludedLowBitCount) & lowByteMask) | prevLowByte);

    source.setByte(byteIndex, lowByte);

    // If there is not bytes left in the data array
    // (the highest is the current), we don't go further.
    if (byteIndex == endByteIndex) {
      return;
    }

    final int excludedHighBitCount = BITS_IN_BYTE - excludedLowBitCount;
    final byte highByteMask = (byte) (byteBitMask >>> excludedHighBitCount);
    final byte prevHighByte = (byte) (source.getByte(byteIndex + 1) & ~highByteMask);

    // Moves the high part of the parameter byte to the low border (beginning) of the byte and
    // unites it with the high part of the target byte that we want to preserve. Also, in case
    // when the high part of the target byte is limited with the high border of the mask, we reset
    // all excluded bits with a high byte mask.
    final byte highByte = (byte) (((value >>> excludedHighBitCount) & highByteMask) | prevHighByte);

    source.setByte(byteIndex + 1, highByte);
  }
}
