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

import java.math.BigInteger;
import java.util.Arrays;

import ru.ispras.fortress.data.types.bitvector.BitVectorAlgorithm.IAction;
import ru.ispras.fortress.data.types.bitvector.BitVectorAlgorithm.IOperation;
import ru.ispras.fortress.util.InvariantChecks;

/**
 * The {@link BitVector} class provides an interface for working with bit vectors ("raw" binary
 * data) of arbitrary size. It provides basic methods for accessing and modifying stored bytes.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public abstract class BitVector implements Comparable<BitVector> {
  /**
   * A constant bit vector that represents the 'false' boolean value (bit size is 1).
   */
  public static final BitVector FALSE = BitVector.unmodifiable(BitVector.valueOf(0, 1));

  /**
   * A constant bit vector that represents the 'true' boolean value (bit size is 1).
   */
  public static final BitVector TRUE = BitVector.unmodifiable(BitVector.valueOf(1, 1));

  /**
   * Number of bits an a byte.
   */
  public final static int BITS_IN_BYTE = 8;

  /**
   * Returns the size of stored data in bits.
   *
   * @return Number of bits.
   */
  public abstract int getBitSize();

  /**
   * Returns the size of stored data in bytes (full number including incomplete bytes).
   *
   * @return Number of bytes (including incomplete bytes).
   */
  public abstract int getByteSize();

  /**
   * Returns the binary value stored in the specified byte. For incomplete bytes, the return value
   * contains only the bits inside the bounds limited by the bit size.
   *
   * @param index Index of the target byte.
   * @return Binary value stored in the specified byte.
   */
  public abstract byte getByte(int index);

  /**
   * Sets the value of the specified byte in the data array. For incomplete bytes, bits that fall
   * beyond the bounds limited by the bit size are ignored. In other words, bits in the target byte
   * that lie beyond the bound retain their values. This requirement is crucial to guarantee correct
   * work of mappings.
   *
   * @param index Index of the target byte.
   * @param value Binary value to be stored in the specified byte.
   */
  public abstract void setByte(int index, byte value);

  /**
   * Returns a boolean flag that corresponds to the value of the specified bit.
   *
   * @param index Bit index.
   * @return {@code true} if the bit is set to {@code 1} or {@code false} otherwise.
   *
   * @throws IndexOutOfBoundsException if the index is out of range.
   */
  public final boolean getBit(final int index) {
    InvariantChecks.checkBounds(index, getBitSize());
    return (getByte(index / BITS_IN_BYTE) & (1 << (index % BITS_IN_BYTE))) != 0;
  }

  /**
   * Sets or resets the specified bit.
   *
   * @param index Bit index.
   * @param value {@code true} to set the bit to {@code 1} or {@code false} to set it to {@code 0}.
   *
   * @throws IndexOutOfBoundsException if the index is out of range.
   */
  public final void setBit(final int index, final boolean value) {
    InvariantChecks.checkBounds(index, getBitSize());

    final int byteIndex = index / BITS_IN_BYTE;
    final byte byteValue = getByte(byteIndex);
    final byte byteMask = (byte) (1 << (index % BITS_IN_BYTE));

    if (value) {
      setByte(byteIndex, (byte)(byteValue | byteMask));
    } else {
      setByte(byteIndex, (byte)(byteValue & ~byteMask));
    }
  }

  /**
   * Sets (sets to one) all bits in the bit vector.
   */
  public final void setAll() {
    BitVectorAlgorithm.fill(this, (byte) -1);
  }

  /**
   * Resets (set to zero) all bits in the bit vector.
   */
  public final void reset() {
    BitVectorAlgorithm.fill(this, (byte) 0);
  }

  /**
   * Checks whether all bits in the bit vector are set (equal to 1).
   *
   * @return {@code true} if all bits are set or {@code false} otherwise.
   */
  public final boolean isAllSet() {
    for (int index = 0; index < getByteSize(); ++index) {
      if (-1 != getByte(index)) {
        return false;
      }
    }
    return true;
  }

  /**
   * Checks whether all bits in the bit vector are reset (equal to 0).
   *
   * @return {@code true} if all bits are reset or {@code false} otherwise.
   */
  public final boolean isAllReset() {
    for (int index = 0; index < getByteSize(); ++index) {
      if (0 != getByte(index)) {
        return false;
      }
    }
    return true;
  }

  /**
   * Copies data from the specified bit vector to the current bit vector. If the bit vector is
   * shorter than the current one, the rest high bytes are filled with zeros. If the source bit
   * vector is longer, the result is truncated (the higher part is skipped).
   *
   * @param src Source it vector.
   */
  public final void assign(final BitVector src) {
    InvariantChecks.checkNotNull(src);
    BitVectorAlgorithm.copy(src, this);
  }

  /***
   * Checks the equality of bit vectors. Bit vectors are considered equal if their sizes match and
   * they hold equal data (comparison is performed byte by byte from the high end to the low end).
   *
   * @param obj A bit vector to be compared with the current bit vector.
   */
  @Override
  public final boolean equals(final Object obj) {
    if (this == obj) {
      return true;
    }

    if (null == obj) {
      return false;
    }

    if (!(obj instanceof BitVector)) {
      return false;
    }

    final BitVector other = (BitVector) obj;
    if (getBitSize() != other.getBitSize()) {
      return false;
    }

    return -1 == BitVectorAlgorithm.mismatchReverse(this, other);
  }

  /**
   * Returns the hash code value for this bit vector. The hash code is calculated based on the
   * stored data bytes.
   *
   * @return The hash code value for bit vector.
   */
  @Override
  public final int hashCode() {
    class Result {
      public int value = 1;
    }

    final Result result = new Result();
    final IAction op = new IAction() {
      @Override
      public void run(final byte v) {
        result.value = 31 * result.value + (v & 0xFF);
      }
    };

    BitVectorAlgorithm.forEach(this, op);
    return result.value;
  }

  /**
   * Compares the current bit vector with the specified bit vector. Data is compared starting with
   * the highest byte in the array.
   *
   * @param other A raw data object.
   * @return 0 if data in both object equals, -1 if the data in the current object is less and 1 of
   *         it is greater.
   *
   * @throws IllegalArgumentException if the {@code other} parameter is {@code null};
   *         if the size of the {@code other} bit vector is different from the size of
   *         the current bit vector.
   */
  @Override
  public final int compareTo(final BitVector other) {
    InvariantChecks.checkNotNull(other);

    if (this == other) {
      return 0;
    }

    final int index = BitVectorAlgorithm.mismatchReverse(this, other);

    // Objects are equal (no mismatch was found)
    if (-1 == index) {
      return 0;
    }

    // This object is less (the value of the highest mismatch byte is less)
    if (((int) getByte(index) & 0xff) < ((int) other.getByte(index) & 0xff)) {
      return -1;
    }

    // This object is greater.
    return 1;
  }

  /**
   * Creates a copy of current bit vector. Creates a new bit vector of the same size and fills it
   * with data from the current bit vector.
   *
   * @return A copy of the current bit vector.
   */
  public final BitVector copy() {
    return new BitVectorStore(this);
  }

  /**
   * Creates a copy of the current bit vector repeated the specified number of times.
   * The size of the resulting bit vector is the size of the current multiplied by
   * the repetition count.
   *
   * @param count Number of times the bit vector will be repeated.
   * @return A copy of the current bit vector repeated the specified number of times.
   *
   * @throws IllegalArgumentException if the new size is {@code <= 0}.
   */
  public final BitVector repeat(final int count) {
    InvariantChecks.checkGreaterThanZero(count);

    final BitVector[] repeat = new BitVector[count];
    Arrays.fill(repeat, this);

    return newMapping(repeat).copy();
  }

  /**
   * Returns a field of the bit vector limited by the specified bounds.
   *
   * @param startBitPos Bit vector that holds start position in bits.
   * @param endBitPos Bit vector that holds end position in bits.
   *
   * @return A field of the bit vector.
   */
  public final BitVector field(final BitVector startBitPos, final BitVector endBitPos) {
    InvariantChecks.checkNotNull(startBitPos);
    InvariantChecks.checkNotNull(endBitPos);
    return field(startBitPos.intValue(), endBitPos.intValue());
  }

  /**
   * Returns a field of the bit vector limited by the specified bounds.
   *
   * @param startBitPos Start position in bits.
   * @param endBitPos End position in bits.
   *
   * @return A field of the bit vector.
   */
  public final BitVector field(final int startBitPos, final int endBitPos) {
    InvariantChecks.checkBounds(startBitPos, getBitSize());
    InvariantChecks.checkBounds(endBitPos, getBitSize());

    final int start = Math.min(startBitPos, endBitPos);
    final int end = Math.max(startBitPos, endBitPos);
    final int size = end - start + 1;

    return newMapping(this, start, size);
  }

  /**
   * Returns a resized copy of the current bit vector.
   *
   * @param newBitSize New size in bits.
   * @param signExt Flag that specifies whether sign extension is required.
   * @return Resized copy of the bit vector.
   *
   * @throws IllegalArgumentException if the new size is {@code <= 0}.
   */
  public BitVector resize(final int newBitSize, final boolean signExt) {
    InvariantChecks.checkGreaterThanZero(newBitSize);

    if (newBitSize == getBitSize()) {
      return copy();
    }

    if (newBitSize < getBitSize()) {
      return copyOf(newMapping(this, 0, newBitSize));
    }

    final BitVector newBitVector = BitVector.newEmpty(newBitSize);
    if (signExt && getBit(getBitSize() - 1)) {
      BitVectorAlgorithm.fill(newBitVector, (byte) 0xFF);
    }

    BitVectorAlgorithm.copy(this, 0, newBitVector, 0, getBitSize());
    return newBitVector;
  }

  /**
   * Returns a copy of the bit vector extended by the specified amount.
   *
   * @param amount Amount in bits.
   * @param signExt Flag that specifies whether sign extension is required.
   * @return Extended copy of the bit vector.
   *
   * @throws IllegalArgumentException if {@code amount} is {@code <= 0}.
   */
  public BitVector extend(final int amount, final boolean signExt) {
    InvariantChecks.checkGreaterThanZero(amount);
    return resize(getBitSize() + amount, signExt);
  }

  /**
   * Creates a copy of the specified bit vector. Creates a new bit vector of the same size and fills
   * it with data from the current bit vector.
   *
   * @param src Source bit vector.
   * @return A copy of the specified bit vector.
   */
  public static BitVector copyOf(final BitVector src) {
    InvariantChecks.checkNotNull(src);
    return src.copy();
  }

  /**
   * Creates an uninitialized bit vector of the specified size.
   *
   * @param bitSize Size of the created bit vector in bits.
   * @return A new bit vector.
   */
  public static BitVector newEmpty(final int bitSize) {
    InvariantChecks.checkGreaterThanZero(bitSize);
    return new BitVectorStore(bitSize);
  }

  /**
   * Creates a bit vector mapping for the current bit vector. The mapping provides access to
   * a part of the bit vector as if it was a separate bit vector.
   *
   * @param source Source bit vector.
   * @param startBitPos The starting position of the mapping.
   * @param bitSize The size of the mapping in bytes.
   * @return A bit vector mapping.
   */
  public static BitVector newMapping(
      final BitVector source,
      final int startBitPos,
      final int bitSize) {
    InvariantChecks.checkNotNull(source);

    if (0 == startBitPos && source.getBitSize() == bitSize) {
      return source;
    }

    InvariantChecks.checkBounds(startBitPos, source.getBitSize());
    InvariantChecks.checkBoundsInclusive(startBitPos + bitSize, source.getBitSize());
    InvariantChecks.checkGreaterThanZero(bitSize);

    if (0 == startBitPos % BITS_IN_BYTE) {
      return new BitVectorMappingAligned(source, startBitPos, bitSize);
    }

    return new BitVectorMapping(source, startBitPos, bitSize);
  }

  /**
   * Creates a mapping for several bit vectors. The mapping unites the bit vector and allows
   * working with them as if they were a single bit vector.
   *
   * @param sources Source bit vectors.
   * @return A bit vector mapping.
   */
  public static BitVector newMapping(final BitVector... sources) {
    InvariantChecks.checkGreaterThanZero(sources.length);

    if (1 == sources.length) {
      return sources[0];
    }

    return new BitVectorMultiMapping(sources);
  }

  /**
   * Returns an unmodifiable view of the specified bit vector. An attempt to modify the bit vector
   * will result in the UnsupportedOperationException exception.
   *
   * @param source Source bit vector.
   * @return Unmodifiable bit vector.
   */
  public static BitVector unmodifiable(final BitVector source) {
    InvariantChecks.checkNotNull(source);

    if (source instanceof BitVectorUnmodifiable) {
      return source;
    }

    return new BitVectorUnmodifiable(source);
  }

  /**
   * Creates a bit vector based on textual representation of binary data. The data size (number of
   * bits) matches the string length.
   *
   * @param bs Textual representation of binary data.
   * @return New bit vector.
   */
  public static BitVector valueOf(final String bs) {
    return valueOf(bs, 2, bs.length());
  }

  /**
   * Returns a bit vector that corresponds to the specified boolean value. IMPORTANT: The returned
   * bit vector is an unmodifiable singleton object. The method is implemented this way to avoid
   * unnecessary memory allocations because bit vectors representing boolean values are not normally
   * modified.
   *
   * @param b Boolean value.
   * @return A constant (!) bit vector for the specified boolean value.
   */
  public static BitVector valueOf(final boolean b) {
    return b ? TRUE : FALSE;
  }

  /**
   * Converts the stored data to a string (binary format).
   *
   * @return Textual representation of the stored data (binary format).
   */
  public final String toString() {
    return toBinString();
  }

  /**
   * Creates a bit vector based on textual representation of binary data. The data size is specified
   * by a method parameter. If the length of the string exceeds the specified size, data is
   * truncated (characters signifying higher bits are ignored). If the string length is less than
   * the data size, the higher bits of the data are filled with zeros.
   *
   * @param text Textual representation of binary data.
   * @param radix Radix to be used during conversion.
   * @param bitSize Size of the resulting bit vector in bits.
   * @return New bit vector.
   *
   * @throws IllegalArgumentException if the {@code text} parameter is {@code null};
   *         if the {@code bitSize} parameter is zero or negative.
   */
  public static BitVector valueOf(final String text, final int radix, final int bitSize) {
    final class BinParser implements IOperation {
      private int bitsRead = 0;

      @Override
      public byte run() {
        byte v = 0;

        do {
          final int bitIndex = text.length() - bitsRead - 1;

          if (bitIndex >= 0) {
            final char c = text.charAt(bitIndex);

            if ('0' != c && '1' != c) {
              throw new NumberFormatException(text);
            }

            v |= (byte) (('0' == c ? 0x0 : 0x1) << (bitsRead % BITS_IN_BYTE));
          }

          ++bitsRead;
        } while (bitsRead != bitSize && 0 != (bitsRead % BITS_IN_BYTE));

        return v;
      }
    };

    final class HexParser implements IOperation {
      private int charIndex = text.length() - 1;

      private byte getNextCharValue() {
        if (charIndex < 0) {
          return 0;
        }

        final char ch = text.charAt(charIndex--);
        if (!(('0' <= ch && ch <= '9') || ('A' <= ch && ch <= 'F') || ('a' <= ch && ch <= 'f'))) {
          throw new NumberFormatException(text);
        }

        return (byte) Character.digit(ch, radix);
      }

      @Override
      public byte run() {
        if (charIndex < 0) {
          return 0;
        }

        final byte low = getNextCharValue();
        final byte high = getNextCharValue();

        return (byte) (low | (high << 4));
      }
    }

    InvariantChecks.checkNotNull(text);
    InvariantChecks.checkGreaterThanZero(bitSize);

    if (2 == radix || 16 == radix) {
      final BitVector result = new BitVectorStore(bitSize);
      BitVectorAlgorithm.generate(result, 2 == radix ? new BinParser() : new HexParser());
      return result;
    }
    return valueOf(new BigInteger(text, radix), bitSize);
  }

  /**
   * Creates a bit vector based on a long value. The data size is specified by a method parameter.
   * If the bit vector size is less that the long value size (64 bits), the value is truncated (high
   * bits of the value are ignored). If the bit vector size exceeds the long value size, high bits
   * of the bit vector are filled with zeros.
   *
   * @param value Long value to be converted to a bit vector.
   * @param bitSize Size of the resulting data array (in bits).
   * @return New bit vector.
   *
   * @throws IllegalArgumentException if the {@code bitSize} parameter is zero or negative.
   */
  public static BitVector valueOf(final long value, final int bitSize) {
    InvariantChecks.checkGreaterThanZero(bitSize);

    final IOperation op = new IOperation() {
      private long v = value;

      @Override
      public byte run() {
        if (0 == v) {
          return 0;
        }

        final byte result = (byte) (v & 0xFFL);
        v >>>= BITS_IN_BYTE;

        return result;
      }
    };

    final BitVector result = new BitVectorStore(bitSize);
    BitVectorAlgorithm.generate(result, op);

    return result;
  }

  /**
   * Creates a bit vector from a byte array.
   *
   * @param data An array of bytes.
   * @param bitSize Size of the resulting bit vector in bits.
   * @return New bit vector.
   *
   * @throws IllegalArgumentException if the {@code data} parameter is {@code null};
   *         if the {@code bitSize} parameter is zero or negative;
   *         if {@code bitSize} does not match to the number ob bytes in the {@code data} array.
   */
  public static BitVector valueOf(final byte[] data, final int bitSize) {
    return new BitVectorStore(data, bitSize);
  }

  /**
   * Creates a bit vector based on a integer value. The data size is specified by a method
   * parameter. If the bit vector is less that the integer value size (32 bits), the value is
   * truncated (high bits of the value are ignored). If the bit vector size exceeds the integer
   * value size, high bits of the raw data store are filled with zeros.
   *
   * @param value Integer value to be converted to a bit array.
   * @param bitSize Size of the resulting data array (in bits).
   * @return New bit vector.
   *
   * @throws IllegalArgumentException if the {@code bitSize} parameter is zero or negative.
   */
  public static BitVector valueOf(final int value, final int bitSize) {
    return valueOf(((long) value) & 0xFFFFFFFFL, bitSize);
  }

  /**
   * Creates a bit vector based on a BigInteger value. The data size is specified by a method
   * parameter. If the bit vector is less than the size of the data stored in BigInteger (
   * returned by the {@code toByteArray} method), the data is truncated (high bits are ignored).
   * If the bit vector size exceeds the data size, the data is sign extended (high bits are
   * filled with zeros for a non-negative value or with ones for a negative value).
   *
   * @param value BigInteger value to be converted to a bit vector.
   * @param bitSize Size of the resulting bit vector (in bits).
   * @return New bit vector.
   *
   * @throws IllegalArgumentException if the {@code value} parameter is {@code null};
   *         if the {@code bitSize} parameter is zero or negative.
   */
  public static BitVector valueOf(final BigInteger value, final int bitSize) {
    InvariantChecks.checkNotNull(value);
    InvariantChecks.checkGreaterThanZero(bitSize);

    final byte[] data = value.toByteArray();
    final byte prefix = (byte) (value.signum() < 0 ? 0xFF : 0x00);

    final BitVector result = new BitVectorStore(bitSize);

    /*
     * NOTE: data is copied in reverse order starting from the highest byte (it goes to the
     * lowest byte of the bit vector). It is implemented this way because the byte order of
     * data received from BigInteger is big-endian, which is opposite from the byte order
     * in bit vectors.
     */
    final int copyStartIndex = data.length - 1;

    final IOperation op = new IOperation() {
      private int index = copyStartIndex;

      @Override
      public byte run() {
        if (index < 0) {
          return prefix;
        }
        return data[index--];
      }
    };

    BitVectorAlgorithm.generate(result, op);
    return result;
  }

  /**
   * Converts the stored data to an integer value. If the bit vector size exceeds integer size (32
   * bits), the data is truncated to 32 bits (high bits are cut off). If the bit vector size is
   * smaller than integer size (32 bits), the high bits of the integer are set to 0 (no sign
   * extension happens).
   *
   * @return Integer representation of the stored value.
   */
  public final int intValue() {
    class Result {public int value = 0;}
    final Result result = new Result();

    final IAction op = new IAction() {
      private int bitCount = 0;

      @Override
      public void run(final byte v) {
        if (bitCount >= Integer.SIZE) {
          return;
        }

        result.value |= (v & 0xFF) << bitCount;
        bitCount += BITS_IN_BYTE;
      }
    };

    BitVectorAlgorithm.forEach(this, op);
    return result.value;
  }

  /**
   * Converts the stored data to an long value. If the stored data size exceeds long size (64 bits),
   * the data is truncated to 64 bits (high bits are cut off).
   *
   * @return Long representation of the stored value.
   */
  public final long longValue() {
    class Result {public long value = 0;}
    final Result result = new Result();

    final IAction op = new IAction() {
      private int bitCount = 0;

      @Override
      public void run(final byte v) {
        if (bitCount >= Long.SIZE) {
          return;
        }

        result.value |= ((long)(v & 0xFF)) << bitCount;
        bitCount += BITS_IN_BYTE;
      }
    };

    BitVectorAlgorithm.forEach(this, op);
    return result.value;
  }

  /**
   * Converts the stored data to a BigInteger value.
   *
   * @return BigInteger representation of the stored value.
   */
  public final BigInteger bigIntegerValue() {
    return bigIntegerValue(true);
  }

  /**
   * Converts the stored data to a BigInteger value.
   *
   * @param signed boolean value indicating should the bit vector be treated as signed integer.
   * @return BigInteger representation of the stored value.
   */
  public final BigInteger bigIntegerValue(final boolean signed) {
    final byte[] byteArray = new byte[this.getByteSize()];

    final IAction op = new IAction() {
      private int index = 0;
      @Override
      public void run(final byte v) {
        byteArray[index++] = v;
      }
    };

    /*
     * NOTE: bytes are copied to the byte array in the reverse order because the
     * constructor of BigInteger requires big-endian byte order (high bytes come first).
     */
    BitVectorAlgorithm.forEachReverse(this, op);

    /*
     * NOTE: If the highest byte is incomplete (only part of it stores a value from the bit vector),
     * it is sign-extended. This is needed to convert bit vectors of all sizes in a uniform way.
     * The BigInteger value is negative if the highest bit of the highest byte in the byte array
     * is set to 1. Consequently, all bit vectors which size is multiple of 8 and the highest bit is
     * set to 1 will be converted to a negative BigInteger. To make this rule work for bit vectors
     * which size is not multiple of 8, this sign extension is implemented.
     */
    final int incompleteBits = getBitSize() % BITS_IN_BYTE;
    final int signBit = byteArray[0] & (1 << (incompleteBits - 1));
    if (signed && 0 != incompleteBits && 0 != signBit) {
      byteArray[0] = (byte)(byteArray[0] | (0xFF << incompleteBits));
    }

    if (signed) {
      return new BigInteger(byteArray);
    }
    return new BigInteger(1, byteArray);
  }

  /**
   * Converts the stored binary data to textual representation.
   *
   * @return Binary string.
   */
  public final String toBinString() {
    final StringBuilder sb = new StringBuilder(getBitSize());

    final IAction op = new IAction() {
      private int totalBitCount = getBitSize();

      @Override
      public void run(final byte v) {
        final int highBits = totalBitCount % BITS_IN_BYTE;
        final int bitCount = (highBits == 0) ? BITS_IN_BYTE : highBits;

        for (int mask = 0x1 << (bitCount - 1); 0 != mask; mask >>>= 1) {
          sb.append((v & mask) == 0 ? '0' : '1');
        }

        totalBitCount -= bitCount;
      }
    };

    BitVectorAlgorithm.forEachReverse(this, op);
    return sb.toString();
  }

  /**
   * Converts the stored binary data to a hexadecimal string.
   *
   * @return Hexadecimal string.
   */
  public final String toHexString() {
    final int HEX_CHARS_IN_BYTE = 2;
    final StringBuilder sb = new StringBuilder(HEX_CHARS_IN_BYTE * getByteSize());

    final IAction op = new IAction() {
      @Override
      public void run(final byte v) {
        if (0 != sb.length()) {
          sb.append(String.format("%0" + HEX_CHARS_IN_BYTE + "X", v));
        } else if (0 != v){
          sb.append(String.format("%X", v));
        }
      }
    };

    BitVectorAlgorithm.forEachReverse(this, op);
    return 0 != sb.length() ? sb.toString() : "0";
  }

  /**
   * Returns a copy of stored data packed into an array of bytes.
   *
   * @return Array of bytes.
   */
  public final byte[] toByteArray() {
    final byte[] byteArray = new byte[this.getByteSize()];

    final IAction op = new IAction() {
      private int index = 0;
      @Override
      public void run(final byte v) {
        byteArray[index++] = v;
      }
    };

    BitVectorAlgorithm.forEach(this, op);
    return byteArray;
  }

  /**
   * Returns the mask for the specified byte in the byte array. The mask helps determine what bits
   * in the specified byte contain meaningful information and which bits should be ignored.
   *
   * @param index Index of the target byte.
   * @return Bit mask for the current byte.
   */
  public final byte getByteBitMask(final int index) {
    InvariantChecks.checkBounds(index, getByteSize());

    final boolean isHighByte = index == getByteSize() - 1;
    if (!isHighByte) {
      return (byte) 0xFF;
    }

    if (0 == highByteMask) {
      final int incompleteBitsInHighByte = getBitSize() % BITS_IN_BYTE;
      highByteMask = (0 == incompleteBitsInHighByte) ?
          (byte) 0xFF : (byte) (0xFF >>> (BITS_IN_BYTE - incompleteBitsInHighByte));
    }

    return highByteMask;
  }

  private byte highByteMask = 0;
}
