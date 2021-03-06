/*
 * Copyright 2012-2018 ISP RAS (http://www.ispras.ru)
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

import java.util.ArrayList;
import java.util.List;

/**
 * The {@link BitVectorMultiMapping} class implements logic that allows concatenating several bit
 * vectors together (allows accessing a group of bit vectors as a single bit vector).
 *
 * <pre>
 * The scheme below demonstrates mapping of two 27-bit data arrays:
 *
 * Initial data:
 *
 * Byte:
 * 4        3        2        1        0  4       3        2         1        0
 *
 * Bit:
 * 32 28!   24       16        8       0  32 28!  24       16        8        0
 * _____________________________________  ____________________________________
 * |    !    |        |        |        | |    !   |        |        |        |
 * |%%%%!    |        |        |        | |%%%%!   |        |        |        |
 * |%%%%!    |        |        |        | |%%%%!   |        |        |        |
 * |____!____|________|________|________| |____!___|________|________|________|
 *
 * <------------------------------------> <----------------------------------->
 *                Bit Vector 1                         Bit Vector 0
 *
 * Mapped view:
 *
 * Byte:
 * 7         6        5        4         3        2        1        0
 *
 * Bit:
 * 56  54!   48       40       32   28!  24       16       8        0
 * _________________________________________________________________
 * |   !     |        |        |     !   |        |        |        |
 * |%%%!     |        |        |     !   |        |        |        |
 * |%%%!     |        |        |     !   |        |        |        |
 * |___!_____|________|________|_____!___|________|________|________|
 *
 *  <-------------------------------><------------------------------>
 *            Bit Vector 1                     Bit Vector 0
 *     <----><-----------------><----><--><------------------------->
 *      Tail        Head          Cut Tail          Head
 *                             <--------->
 *                             Linking Byte
 * </pre>
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
final class BitVectorMultiMapping extends BitVector {
  /**
   * The {@link LinkingByteMapping} class is a special mapping that helps concatenate two bit
   * vectors. It is needed to concatenate the incomplete high byte of one bit vector with the
   * complementary low part of another. Both part together should make up a complete single byte.
   *
   * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
   */
  private static final class LinkingByteMapping extends BitVector {
    private final BitVector lowPart;
    private final BitVector highPart;

    /**
     * Creates a {@link LinkingByteMapping} object from two parts.
     *
     * @param lowPart A low part of the linking byte (a bit vector, which size is less than 8).
     * @param highPart A high part of the linking byte (a bit vector, which size is less than 8).
     */
    public LinkingByteMapping(final BitVector lowPart, final BitVector highPart) {
      InvariantChecks.checkTrue(0 < lowPart.getBitSize() && lowPart.getBitSize() < BITS_IN_BYTE);
      InvariantChecks.checkTrue(0 < highPart.getBitSize() && highPart.getBitSize() < BITS_IN_BYTE);
      InvariantChecks.checkTrue(lowPart.getBitSize() + highPart.getBitSize() <= BITS_IN_BYTE);

      this.lowPart = lowPart;
      this.highPart = highPart;
    }

    @Override
    public int getBitSize() {
      return lowPart.getBitSize() + highPart.getBitSize();
    }

    /**
     * {@inheritDoc} NOTE: The number of bytes a {@link LinkingByteMapping} object can store
     * always equals {@code 1}.
     */
    @Override
    public int getByteSize() {
      return 1;
    }

    /**
     * {@inheritDoc} NOTE: A LinkingByteMapping object always stores 1-byte data and, consequently,
     * accepts only 0 as the value of the index parameter.
     */
    @Override
    public byte getByte(final int index) {
      InvariantChecks.checkTrue(0 == index, "ONE-BYTE DATA ARRAY!");

      final byte lowValue = lowPart.getByte(0);
      final byte highValue = highPart.getByte(0);

      final byte result =
          (byte) (((highValue << lowPart.getBitSize()) | lowValue) & getByteBitMask(0));

      return result;
    }

    /**
     * {@inheritDoc} NOTE: A {@link LinkingByteMapping} object always stores 1-byte data and,
     * consequently, accepts only {@code 0} as the value of the index parameter.
     */
    @Override
    public void setByte(final int index, final byte value) {
      InvariantChecks.checkTrue(0 == index, "ONE-BYTE DATA ARRAY!");

      final byte lowValue = (byte) ((value & ~(0xFF << lowPart.getBitSize())));

      final byte highValue =
          (byte) ((value >> lowPart.getBitSize()) & ~(0xFF << highPart.getBitSize()));

      lowPart.setByte(0, lowValue);
      highPart.setByte(0, highValue);
    }
  }

  /**
   * The {@link ByteAccessor} class is aimed to provide access to an arbitrary byte of the mapping.
   * The class encapsulates the real data source (part of the mapping that actually contains
   * the needed byte) and the relative index of the byte in that data source.
   *
   * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
   */
  private static final class ByteAccessor {
    public final BitVector data;
    public final int index;

    /**
     * Creates an instance of the {@link ByteAccessor} class.
     *
     * @param data Data array that hold the specified byte.
     * @param index The relative index of the byte in the data array.
     */
    public ByteAccessor(final BitVector data, final int index) {
      this.data = data;
      this.index = index;
    }

    /**
     * Returns the value of the byte the accessor refers to.
     *
     * @return A target byte value.
     */
    public byte getByte() {
      return data.getByte(index);
    }

    /**
     * Sets the value of the byte the accessor refers to.
     *
     * @param value The value to be assign to the target byte.
     */
    public void setByte(final byte value) {
      data.setByte(index, value);
    }
  }

  private final List<ByteAccessor> byteAccessors;
  private final int bitSize;

  /**
   * Adds byte accessors for the specified data array to the vector of byte accessors that build
   * up the mapping. Returns the size of processed data in bits.
   *
   * @param data The data array to be mapped to the vector of byte accessors.
   * @return The size of processed data in bits (number of bits in the source data array).
   */
  private int addByteAcessors(final BitVector data) {
    for (int index = 0; index < data.getByteSize(); ++index) {
      byteAccessors.add(new ByteAccessor(data, index));
    }

    return data.getBitSize();
  }

  /**
   * Creates a mapping that concatenates bit vectors provided in the specified array.
   *
   * <p>NOTE: The order of bit vectors in the array must be from high to low.
   * That is the array looks like this:
   * <pre>
   * {HIGH, ..., LOW}
   *  [0]       [N-1]</pre>
   * while the concatenation result looks like this:
   * <pre>
   * |HIGH|...|LOW|
   * M            0</pre>
   * {@code N} is the number of bit vectors to be concatenated;
   * {@code M} is the total bit size of the concatenation result.</p>
   *
   * @param bitVectors Array of bit vectors to be concatenated.
   *
   * @throws IllegalArgumentException if the argument is {@code null}, if it is an empty array
   *         or if the array contains {@code null} objects.
   */
  public BitVectorMultiMapping(final BitVector[] bitVectors) {
    InvariantChecks.checkNotEmpty(bitVectors);
    byteAccessors = new ArrayList<ByteAccessor>();

    BitVector unusedPrevPart = null;
    int processedBitSize = 0;

    for (int index = bitVectors.length - 1; index >= 0; index--) {
      final BitVector data = bitVectors[index];
      InvariantChecks.checkNotNull(data);

      int offset = 0;
      if (null != unusedPrevPart) {
        final int bitsToCompleteByte = BITS_IN_BYTE - unusedPrevPart.getBitSize();
        InvariantChecks.checkTrue(bitsToCompleteByte > 0);

        final BitVector currentCutPart = (data.getBitSize() <= bitsToCompleteByte)
            ? data : BitVector.newMapping(data, 0, bitsToCompleteByte);

        final BitVector linkingBlock = new LinkingByteMapping(unusedPrevPart, currentCutPart);
        if (linkingBlock.getBitSize() < BITS_IN_BYTE) {
          unusedPrevPart = linkingBlock;
        } else {
          processedBitSize += addByteAcessors(linkingBlock);
          unusedPrevPart = null;
        }

        offset = currentCutPart.getBitSize();
      }

      final int dataSize = data.getBitSize() - offset;
      if (0 == dataSize) {
        continue;
      }

      /*
       * We split data in the current data object in to parts (excluding the part that was taken to
       * create a linking byte with the unused part of the previous data object): head and tail. The
       * head size is proportional to the number of bits in a byte. We create for it corresponding
       * entries in the byte accessor vector. Tail contains the rest of the data. Its size is
       * ALLWAYS LESS than the number of bits in a byte. This is the unused part of the current data
       * object to be used to build a linking byte with the lowest part of the next data object.
       */
      final int headBitSize = (dataSize / BITS_IN_BYTE) * BITS_IN_BYTE;
      final int tailBitSize = dataSize % BITS_IN_BYTE;

      if (0 != headBitSize) {
        final boolean headTakesAllData = (0 == offset) && (0 == tailBitSize);
        final BitVector currentBlock = headTakesAllData
            ? data : BitVector.newMapping(data, offset, headBitSize);

        processedBitSize += addByteAcessors(currentBlock);
      }

      if (0 != tailBitSize) {
        final boolean tailTakesAllData = (0 == offset) && (0 == headBitSize);
        unusedPrevPart = tailTakesAllData
            ? data : BitVector.newMapping(data, offset + headBitSize, tailBitSize);
      }
    }

    // If any unused data is left, we process it.
    if (null != unusedPrevPart) {
      processedBitSize += addByteAcessors(unusedPrevPart);
    }

    this.bitSize = processedBitSize;
  }

  @Override
  public int getBitSize() {
    return bitSize;
  }

  @Override
  public int getByteSize() {
    return byteAccessors.size();
  }

  @Override
  public byte getByte(final int index) {
    InvariantChecks.checkBounds(index, getByteSize());

    final ByteAccessor accessors = byteAccessors.get(index);
    return accessors.getByte();
  }

  @Override
  public void setByte(final int index, final byte value) {
    InvariantChecks.checkBounds(index, getByteSize());

    final ByteAccessor accessors = byteAccessors.get(index);
    accessors.setByte(value);
  }
}
