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

import static ru.ispras.fortress.util.InvariantChecks.checkBounds;
import static ru.ispras.fortress.util.InvariantChecks.checkGreaterThanZero;
import static ru.ispras.fortress.util.InvariantChecks.checkNotNull;

/**
 * The BitVectorStore class represents a data array that stores binary data of a bit vector. Data
 * can be accessed by bytes. If the number of bits is not multiple of 8 (number of bits in a byte)
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

final class BitVectorStore extends BitVector {
  private final byte[] dataBytes; // Array that stores binary data.
  private final int bitSize; // Number of used bits.

  /**
   * Allocates a bit vector.
   * 
   * @param bitSize Data size in bits.
   */

  public BitVectorStore(int bitSize) {
    checkGreaterThanZero(bitSize);

    final int byteSize = bitSize / BITS_IN_BYTE + (0 == (bitSize % BITS_IN_BYTE) ? 0 : 1);

    this.bitSize = bitSize;
    this.dataBytes = new byte[byteSize];

    reset();
  }

  /**
   * Creates a copy of existing an bit vector.
   * 
   * @param src An existing bit vector to be copied.
   */

  public BitVectorStore(BitVector src) {
    checkNotNull(src);

    this.dataBytes = new byte[src.getByteSize()];
    this.bitSize = src.getBitSize();

    assign(src);
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
    return dataBytes.length;
  }

  /**
   * {@inheritDoc}
   */

  @Override
  public byte getByte(int index) {
    checkBounds(index, getByteSize());
    return (byte) (dataBytes[index] & getByteBitMask(index));
  }

  /**
   * {@inheritDoc}
   */

  @Override
  public void setByte(int index, byte value) {
    checkBounds(index, getByteSize());

    final byte mask = getByteBitMask(index);
    final byte old = dataBytes[index];

    // Bits beyond the range <bitCount-1..0> are preserved.
    dataBytes[index] = (byte) ((old & ~mask) | (value & mask));

    // To make sure that bits beyond the bound have not been changed.
    assert ((byte) (old & ~mask)) == ((byte) (dataBytes[index] & ~mask));
  }
}
