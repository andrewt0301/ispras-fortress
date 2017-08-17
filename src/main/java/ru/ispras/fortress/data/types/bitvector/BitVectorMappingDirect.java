/*
 * Copyright 2017 ISP RAS (http://www.ispras.ru)
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

import static ru.ispras.fortress.util.InvariantChecks.checkGreaterThanZero;

import ru.ispras.fortress.util.InvariantChecks;

/**
 * The {@link BitVectorMappingDirect} class provides the possibility to map a bit vector to another
 * bit vector. This class is for special cases when the start and positions of the mapping 
 * are at the byte border.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
final class BitVectorMappingDirect extends BitVector {
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
  public BitVectorMappingDirect(
      final BitVector src,
      final int beginBitPos,
      final int bitSize) {
    InvariantChecks.checkNotNull(src);
    InvariantChecks.checkGreaterThanZero(bitSize);

    InvariantChecks.checkBounds(beginBitPos, src.getBitSize());
    InvariantChecks.checkBoundsInclusive(beginBitPos + bitSize, src.getBitSize());

    InvariantChecks.checkTrue(0 == beginBitPos % BITS_IN_BYTE);
    InvariantChecks.checkTrue(0 == bitSize % BITS_IN_BYTE);

    this.source = src;
    this.bitSize = bitSize;
    this.byteSize = bitSize / BITS_IN_BYTE;
    this.byteOffset =  beginBitPos / BITS_IN_BYTE;
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
    return source.getByte(byteOffset + index);
  }

  /**
   * {@inheritDoc}
   */
  @Override
  public void setByte(final int index, final byte value) {
    InvariantChecks.checkBounds(index, getByteSize());
    source.setByte(byteOffset + index, value);
  }
}
