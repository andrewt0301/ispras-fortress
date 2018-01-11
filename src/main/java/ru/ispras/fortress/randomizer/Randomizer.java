/*
 * Copyright 2007-2015 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.randomizer;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;

import ru.ispras.fortress.data.types.bitvector.BitVector;
import ru.ispras.fortress.data.types.bitvector.BitVectorAlgorithm;
import ru.ispras.fortress.util.BitUtils;
import ru.ispras.fortress.util.InvariantChecks;

/**
 * This class is a wrapper around a random number generator. It is responsible for generating random
 * objects (numbers, strings, etc.) and filling storages (arrays, collections, etc.) with random
 * data.
 *
 * @author <a href="mailto:kamkin@ispras.ru">Alexander Kamkin</a>
 */
public final class Randomizer {
  /** Randomizer instance (singleton). */
  private static Randomizer randomizer = new Randomizer();

  /** {@link BigInteger} for {@link Long#MAX_VALUE} */
  private static final BigInteger MAX_LONG = BigInteger.valueOf(Long.MAX_VALUE);

  /**
   * Returns the randomizer instance.
   *
   * @return the randomizer instance.
   */
  public static Randomizer get() {
    return randomizer;
  }

  /** The random number generator used by the randomizer. */
  private RandomGenerator generator = new ModifiedLaggedFibonacci();

  /**
   * The randomizer constructor is private.
   */
  private Randomizer() {
    // Do nothing.
  }

  /**
   * Returns the current random number generator.
   *
   * @return the random number generator.
   */
  public RandomGenerator getGenerator() {
    return generator;
  }

  /**
   * Sets the current random number generator.
   *
   * @param generator the random number generator to be set.
   */
  public void setGenerator(final RandomGenerator generator) {
    this.generator = generator;
  }

  /**
   * Sets the new seed of the random number generator.
   *
   * @param seed the seed to be set.
   */
  public void setSeed(final int seed) {
    generator.seed(seed);
  }

  //------------------------------------------------------------------------------------------------
  // Next Methods (Random Number Generators for Different Integer Types)
  //------------------------------------------------------------------------------------------------

  /**
   * Generates the next random integer value.
   *
   * @return the next random integer number.
   */
  public int next() {
    return generator.next();
  }

  /**
   * Generates the next random boolean.
   *
   * @return A random boolean.
   */
  public boolean nextBoolean() {
    return (next() & 1) != 0 ? true : false;
  }

  /**
   * Generates the next random byte.
   *
   * @return A random byte.
   */
  public byte nextByte() {
    return (byte) next();
  }

  /**
   * Generates the next random char.
   *
   * @return A random char.
   */
  public char nextChar() {
    return (char) next();
  }

  /**
   * Generates the next random int.
   *
   * @return A random int.
   */
  public int nextInt() {
    return (int) next();
  }

  /**
   * Generates the next random long.
   *
   * @return A random long.
   */
  public long nextLong() {
    return ((long) next() << Integer.SIZE) | ((long) next() & 0xffffFFFFL);
  }

  //------------------------------------------------------------------------------------------------
  // Next Integer Methods
  //------------------------------------------------------------------------------------------------

  private int nextNonNegativeInt() {
    return (nextInt() & (-1 >>> 1));
  }

  private int nextNonNegativeIntLess(final int max) {
    return nextNonNegativeInt() % max;
  }

  private int nextNonNegativeIntLessOrEqual(final int max) {
    if (max == Integer.MAX_VALUE) {
      return nextNonNegativeInt();
    }

    return nextNonNegativeIntLess(max + 1);
  }

  /**
   * Returns a random number from the given range (inclusive).
   *
   * @param min the low bound of the range.
   * @param max the high bound of the range.
   * @return a random number.
   */
  public int nextIntRange(final int min, final int max) {
    if (min > max) {
      throw new IllegalArgumentException("min is greater than max");
    }

    if (max >= 0 && min >= max - Integer.MAX_VALUE || max < 0 && max <= Integer.MAX_VALUE + min) {
      return min + nextNonNegativeIntLessOrEqual(max - min);
    }

    final int rnd = nextInt();

    if (rnd < min) {
      return (rnd - Integer.MIN_VALUE) + min;
    }

    if (rnd > max) {
      return max - (Integer.MAX_VALUE - rnd);
    }

    return rnd;
  }

  /**
   * Returns a random number of the given bit size (width).
   *
   * @param width the bit size.
   * @return a random number.
   */
  public int nextIntField(final int width) {
    return next() & BitUtils.getIntegerMask(width);
  }

  /**
   * Returns a number with the randomized range of bits (field).
   *
   * @param lo the low bound of the field.
   * @param hi the high bound of the field.
   * @return a random number.
   */
  public int nextIntField(final int lo, final int hi) {
    return next() & BitUtils.getIntegerMask(lo, hi);
  }

  //------------------------------------------------------------------------------------------------
  // Next Long Methods
  //------------------------------------------------------------------------------------------------

  private long nextNonNegativeLong() {
    return (nextLong() & (-1L >>> 1));
  }

  private long nextNonNegativeLongLess(final long max) {
    return nextNonNegativeLong() % max;
  }

  private long nextNonNegativeLongLessOrEqual(final long max) {
    if (max == Long.MAX_VALUE) {
      return nextNonNegativeLong();
    }

    return nextNonNegativeLongLess(max + 1);
  }


  /**
   * Returns a random number from the given range.
   *
   * @param min the low bound of the range.
   * @param max the high bound of the range.
   * @return a random number.
   */
  public long nextLongRange(final long min, final long max) {
    if (min > max) {
      throw new IllegalArgumentException("min is greater than max");
    }

    if (max >= 0 && min >= max - Long.MAX_VALUE || max < 0 && max <= Long.MAX_VALUE + min) {
      return min + nextNonNegativeLongLessOrEqual(max - min);
    }

    final long rnd = nextLong();

    if (rnd < min) {
      return (rnd - Long.MIN_VALUE) + min;
    }

    if (rnd > max) {
      return max - (Long.MAX_VALUE - rnd);
    }

    return rnd;
  }

  /**
   * Returns a random number of the given bit size (width).
   *
   * @param width the bit size.
   * @return a random number.
   */
  public long nextLongField(final int width) {
    return nextLong() & BitUtils.getLongMask(width);
  }

  /**
   * Returns a number with the randomized range of bits (field).
   *
   * @param lo the low bound of the field.
   * @param hi the high bound of the field.
   * @return a random number.
   */
  public long nextLongField(final int lo, final int hi) {
    return nextLong() & BitUtils.getLongMask(lo, hi);
  }

  //------------------------------------------------------------------------------------------------
  // Next Big Integer Methods
  //------------------------------------------------------------------------------------------------

  /**
   * Returns a random number of the given bit size (width).
   *
   * @param width the bit size.
   * @param signed flag indicating that the result must be a signed value.
   * @return a random number.
   */
  public BigInteger nextBigIntegerField(final int width, final boolean signed) {
    final BitVector data = BitVector.newEmpty(width);

    fill(data);

    return data.bigIntegerValue(signed);
  }

  /**
   * Returns a random number from the given range.
   *
   * @param min the low bound of the range.
   * @param max the high bound of the range.
   * @return a random number.
   */
  public BigInteger nextBigIntegerRange(final BigInteger min, final BigInteger max) {
    InvariantChecks.checkNotNull(min);
    InvariantChecks.checkNotNull(max);
    InvariantChecks.checkGreaterOrEq(max, min);

    final BigInteger diff = max.subtract(min);
    final BigInteger offset;

    if (diff.compareTo(MAX_LONG) <= 0) {
      offset = BigInteger.valueOf(nextLongRange(0, diff.longValue()));
    } else {
      final BigInteger first = nextBigIntegerRange(BigInteger.ZERO, MAX_LONG);
      final BigInteger second = nextBigIntegerRange(BigInteger.ZERO, diff.subtract(MAX_LONG));
      offset = first.add(second);
     }

    return min.add(offset);
  }

  //------------------------------------------------------------------------------------------------
  // Choose Methods
  //------------------------------------------------------------------------------------------------

  /**
   * Chooses a random item of the given array.
   *
   * @param array the array whose items are chosen.
   * @param <T> array item type.
   * @return a random item of the array.
   * @throws IllegalArgumentException if {@code array == null};
   *         if {@code array} is empty.
   */
  public <T> T choose(final T[] array) {
    InvariantChecks.checkNotEmpty(array);

    return array[nextIntRange(0, array.length - 1)];
  }

  /**
   * Chooses a random item of the given collection.
   *
   * @param collection the collection whose items are chosen.
   * @param <T> collection item type.
   * @return a random item of the collection.
   * @throws IllegalArgumentException if {@code collection == null};
   *         if {@code collection} is empty.
   */
  public <T> T choose(final Collection<T> collection) {
    InvariantChecks.checkNotEmpty(collection);

    final ArrayList<T> arrayList = new ArrayList<>(collection);
    return arrayList.get(nextIntRange(0, collection.size() - 1));
  }

  //------------------------------------------------------------------------------------------------
  // Permute Methods
  //------------------------------------------------------------------------------------------------

  /**
   * Permute items of the given array.
   *
   * @param array the array whose items to be permuted.
   * @param <T> array item type.
   *
   * @throws IllegalArgumentException if {@code array == null}.
   */
  public <T> void permute(final T[] array) {
    InvariantChecks.checkNotNull(array);

    for (int i = 0; i < array.length; i++) {
      final int j = nextIntRange(0, array.length - 1);
      final int k = nextIntRange(0, array.length - 1);

      final T temp = array[j];

      array[j] = array[k];
      array[k] = temp;
    }
  }

  //------------------------------------------------------------------------------------------------
  // Fill Methods
  //------------------------------------------------------------------------------------------------

  /**
   * Fills the byte array with random data.
   *
   * @param data the array to be randomized.
   */
  public void fill(final byte[] data) {
    for (int i = 0; i < data.length; i++) {
      data[i] = nextByte();
    }
  }

  /**
   * Fills the char array with random data.
   *
   * @param data the array to be randomized.
   */
  public void fill(final char[] data) {
    for (int i = 0; i < data.length; i++) {
      data[i] = nextChar();
    }
  }

  /**
   * Fills the int array with random data.
   *
   * @param data the array to be randomized.
   */
  public void fill(final int[] data) {
    for (int i = 0; i < data.length; i++) {
      data[i] = nextInt();
    }
  }

  /**
   * Fills the long array with random data.
   *
   * @param data the array to be randomized.
   */
  public void fill(final long[] data) {
    for (int i = 0; i < data.length; i++) {
      data[i] = nextLong();
    }
  }

  /**
   * Fills the raw data storage with random data.
   *
   * @param data the raw data storage to be randomized.
   */
  public void fill(final BitVector data) {
    BitVectorAlgorithm.generate(data, new BitVectorAlgorithm.IOperation() {
      @Override
      public byte run() {
        return nextByte();
      }
    });
  }
}
