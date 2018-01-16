/*
 * Copyright 2007-2018 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.util;

import java.math.BigInteger;

/**
 * {@link BitUtils} class implements some methods for manipulating with bits.
 *
 * @author <a href="mailto:kamkin@ispras.ru">Alexander Kamkin</a>
 */
public final class BitUtils {
  private BitUtils() {}

  /**
   * Returns a bit mask of the given width.
   *
   * @param width Mask width.
   * @return Integer bit mask.
   */
  public static int getIntegerMask(final int width) {
    InvariantChecks.checkBoundsInclusive(width, Integer.SIZE);
    return width >= Integer.SIZE ? -1 : (1 << width) - 1;
  }

  /**
   * Returns a bit mask for the given range.
   *
   * @param lo Lower bound.
   * @param hi Higher bound.
   * @return Integer bit mask.
   */
  public static int getIntegerMask(final int lo, final int hi) {
    InvariantChecks.checkBounds(lo, Integer.SIZE);
    InvariantChecks.checkBounds(hi, Integer.SIZE);
    InvariantChecks.checkGreaterOrEq(hi, lo);

    return getIntegerMask((hi - lo) + 1) << lo;
  }

  /**
   * Returns the field of the given value.
   *
   * @param value Value.
   * @param lo Lower bound.
   * @param hi Higher bound.
   * @return Value field.
   */
  public static int getField(final int value, final int lo, final int hi) {
    InvariantChecks.checkBounds(lo, Integer.SIZE);
    InvariantChecks.checkBounds(hi, Integer.SIZE);
    InvariantChecks.checkGreaterOrEq(hi, lo);

    return (value & getIntegerMask(lo, hi)) >>> lo;
  }

  /**
   * Returns the field of the given value.
   *
   * @param value Value.
   * @param lo Lower bound.
   * @param hi Higher bound.
   * @return Value field.
   */
  public static long getField(final long value, final int lo, final int hi) {
    InvariantChecks.checkBounds(lo, Long.SIZE);
    InvariantChecks.checkBounds(hi, Long.SIZE);
    InvariantChecks.checkGreaterOrEq(hi, lo);

    return (value & getLongMask(lo, hi)) >>> lo;
  }

  /**
   * Returns the field of the given value.
   *
   * @param value Value.
   * @param lo Lower bound.
   * @param hi Higher bound.
   * @return Value field.
   */
  public static BigInteger getField(final BigInteger value, final int lo, final int hi) {
    InvariantChecks.checkNotNull(value);
    InvariantChecks.checkGreaterOrEqZero(lo);
    InvariantChecks.checkGreaterOrEqZero(hi);
    InvariantChecks.checkGreaterOrEq(hi, lo);

    return value.and(getBigIntegerMask(lo, hi)).shiftRight(lo);
  }

  /**
   * Sets the field to the given value.
   *
   * @param value Value.
   * @param lo Lower bound.
   * @param hi Higher bound.
   * @param field Field.
   * @return Value with the updated field.
   */
  public static int setField(final int value, final int lo, final int hi, final int field) {
    InvariantChecks.checkBounds(lo, Integer.SIZE);
    InvariantChecks.checkBounds(hi, Integer.SIZE);
    InvariantChecks.checkGreaterOrEq(hi, lo);

    return (value & ~getIntegerMask(lo, hi)) | (field << lo);
  }

  /**
   * Sets the field to the given value.
   *
   * @param value Value.
   * @param lo Lower bound.
   * @param hi Higher bound.
   * @param field Field.
   * @return Value with the updated field.
   */
  public static long setField(final long value, final int lo, final int hi, final long field) {
    InvariantChecks.checkBounds(lo, Long.SIZE);
    InvariantChecks.checkBounds(hi, Long.SIZE);
    InvariantChecks.checkGreaterOrEq(hi, lo);

    return (value & ~getLongMask(lo, hi)) | (field << lo);
  }

  /**
   * Sets the field to the given value.
   *
   * @param value Value.
   * @param lo Lower bound.
   * @param hi Higher bound.
   * @param field Field.
   * @return Value with the updated field.
   */
  public static BigInteger setField(
      final BigInteger value, final int lo, final int hi, final BigInteger field) {
    InvariantChecks.checkNotNull(value);
    InvariantChecks.checkNotNull(field);
    InvariantChecks.checkGreaterOrEqZero(lo);
    InvariantChecks.checkGreaterOrEqZero(hi);
    InvariantChecks.checkGreaterOrEq(hi, lo);

    return value.andNot(getBigIntegerMask(lo, hi)).or(field.shiftLeft(lo));
  }

  /**
   * Returns the bit mask of the given width.
   *
   * @param width Mask width.
   * @return {@link Long} bit mask.
   */
  public static long getLongMask(final int width) {
    InvariantChecks.checkBoundsInclusive(width, Long.SIZE);
    return width >= Long.SIZE ? -1L : (1L << width) - 1;
  }

  /**
   * Returns the bit mask for the given range.
   *
   * @param lo Lower bound.
   * @param hi Higher bound.
   * @return {@link Long} bit mask.
   */
  public static long getLongMask(final int lo, final int hi) {
    InvariantChecks.checkBounds(lo, Long.SIZE);
    InvariantChecks.checkBounds(hi, Long.SIZE);
    InvariantChecks.checkGreaterOrEq(hi, lo);

    return getLongMask((hi - lo) + 1) << lo;
  }

  /**
   * Returns the bit mask for the given width.
   *
   * @param width Mask width.
   * @return {@link BigInteger} bit mask.
   */
  public static BigInteger getBigIntegerMask(final int width) {
    InvariantChecks.checkGreaterOrEqZero(width);
    return BigInteger.ONE.shiftLeft(width).subtract(BigInteger.ONE);
  }

  /**
   * Returns the bit mask for the given range.
   *
   * @param lo Lower bound.
   * @param hi Higher bound.
   * @return {@link BigInteger} bit mask.
   */
  public static BigInteger getBigIntegerMask(final int lo, final int hi) {
    InvariantChecks.checkGreaterOrEqZero(lo);
    InvariantChecks.checkGreaterOrEqZero(hi);
    InvariantChecks.checkGreaterOrEq(hi, lo);

    return getBigIntegerMask((hi - lo) + 1).shiftLeft(lo);
  }
}
