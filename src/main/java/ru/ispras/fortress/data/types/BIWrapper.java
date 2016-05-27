/*
 * Copyright 2012-2014 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.data.types;

import java.math.BigInteger;

import ru.ispras.fortress.util.InvariantChecks;

/**
 * The BIWrapper class provides a wrapper around the BigInteger class to conveniently store and
 * convert binary data.
 * 
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
@Deprecated
public final class BIWrapper {
  /**
   * The BITS_IN_HEX constant specifies the number of bit a buffer should contain to be represented
   * by one hexadecimal character (a hexadecimal number of length 1).
   */
  private static final int BITS_IN_HEX = 4;

  private final BigInteger value;
  private final int size;
  private final int radix;

  /**
   * Constructs a BIWrapper object from a BigInteger value.
   * 
   * @param value A BitVectorWrapper object that stores data.
   * @param size The size of the data in bits.
   * @param radix The radix that will be used in data conversions.
   */
  public BIWrapper(final BigInteger value, final int size, final int radix) {
    InvariantChecks.checkNotNull(value);
    InvariantChecks.checkGreaterThanZero(size);
    InvariantChecks.checkGreaterThanZero(radix);

    this.value = value;
    this.size = size;
    this.radix = radix;
  }

  /**
   * A factory method that creates a BIWrapper object from a string representation.
   * 
   * @param value The string representation of the data.
   * @param radix The radix that will be used in to convert the string to a BigInteger object.
   * @param size The size of the data in bits.
   * @param typeRadix The radix that will be used to convert the data object to string.
   * @return object of BitVectorWrapper
   */
  public static BIWrapper valueOf(
      final String value,
      final int radix,
      final int size,
      final int typeRadix) {
    return new BIWrapper(new BigInteger(value, radix), size, typeRadix);
  }

  /**
   * Converts the stored data into a binary string.
   * 
   * @return A string representing the stored value in binary format.
   */
  public String toBinString() {
    final String binstr = value.toString(Radix.BIN.value());
    final int count = size - binstr.length();

    return (count > 0) ? String.format("%0" + count + "d", 0) + binstr : binstr;
  }

  /**
   * Converts the stored data into a hexadecimal string.
   * 
   * @return A string representing the stored value in hexadecimal format.
   */
  public String toHexString() {
    final String hexstr = value.toString(Radix.HEX.value());
    final int count = size / BITS_IN_HEX - hexstr.length();

    return (count > 0) ? String.format("%0" + count + "d", 0) + hexstr : hexstr;
  }

  /**
   * Converts the stored data to a string (the string format depends on radix).
   * 
   * @return The string representation of the stored data.
   */
  @Override
  public String toString() {
    if (radix == Radix.HEX.value()) {
      return toHexString();
    }

    if (radix == Radix.BIN.value()) {
      return toBinString();
    }

    assert false;
    return value.toString();
  }

  /**
   * Returns a BigInteger object which is the internal representation of the stored data.
   * 
   * @return A BigInteger object that holds the data (the internal representation).
   */
  public BigInteger getValue() {
    return value;
  }

  /**
   * Returns the size of the stored data in bits.
   * 
   * @return Data size in bits.
   */
  public int getSize() {
    return size;
  }

  /**
   * Returns the radix that is used to translate data to/from a string.
   * 
   * @return The radix value.
   */
  public int getRadix() {
    return radix;
  }

  /**
   * {@inheritDoc}
   */
  @Override
  public int hashCode() {
    final int prime = 31;
    int result = 1;

    result = prime * result + size;
    result = prime * result + value.hashCode();

    return result;
  }

  /**
   * {@inheritDoc}
   */
  @Override
  public boolean equals(final Object obj) {
    if (this == obj) {
      return true;
    }

    if (obj == null) {
      return false;
    }

    if (getClass() != obj.getClass()) {
      return false;
    }

    final BIWrapper other = (BIWrapper) obj;
    if (size != other.size) {
      return false;
    }

    return value.equals(other.value);
  }
}
