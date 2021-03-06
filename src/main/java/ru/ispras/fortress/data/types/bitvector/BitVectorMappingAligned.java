/*
 * Copyright 2017-2018 ISP RAS (http://www.ispras.ru)
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
 * The {@link BitVectorMappingAligned} class provides the possibility to map a bit vector to another
 * bit vector. This class is for the special case when the start position of the mapping
 * is byte-aligned.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
final class BitVectorMappingAligned extends BitVector {
  private final BitVector source;
  private final int bitSize;
  private final int byteSize;
  private final int byteOffset;

  /**
   * Creates a mapping for the specified bit vector.
   *
   * @param src The source bit vector.
   * @param beginBitPos The starting position of the mapping.
   * @param bitSize The length of the mapping in bits.
   */
  public BitVectorMappingAligned(
      final BitVector src,
      final int beginBitPos,
      final int bitSize) {
    InvariantChecks.checkNotNull(src);
    InvariantChecks.checkGreaterThanZero(bitSize);

    InvariantChecks.checkBounds(beginBitPos, src.getBitSize());
    InvariantChecks.checkBoundsInclusive(beginBitPos + bitSize, src.getBitSize());
    InvariantChecks.checkTrue(0 == beginBitPos % BITS_IN_BYTE);

    this.source = src;
    this.bitSize = bitSize;
    this.byteSize = bitSize / BITS_IN_BYTE + (0 == bitSize % BITS_IN_BYTE ? 0 : 1);
    this.byteOffset =  beginBitPos / BITS_IN_BYTE;
  }

  @Override
  public int getBitSize() {
    return bitSize;
  }

  @Override
  public int getByteSize() {
    return byteSize;
  }

  @Override
  public byte getByte(final int index) {
    InvariantChecks.checkBounds(index, getByteSize());
    final int byteIndex = byteOffset + index;
    return (byte) (source.getByte(byteIndex) & getByteBitMask(index));
  }

  @Override
  public void setByte(final int index, final byte value) {
    InvariantChecks.checkBounds(index, getByteSize());

    final int byteIndex = byteOffset + index;
    final byte mask = getByteBitMask(index);

    if (mask == ((byte) 0xFF)) {
      source.setByte(byteIndex, value);
    } else {
      final byte mergedValue =  (byte)((value & mask) | (source.getByte(byteIndex) & ~mask));
      source.setByte(byteIndex, mergedValue);
    }
  }
}
