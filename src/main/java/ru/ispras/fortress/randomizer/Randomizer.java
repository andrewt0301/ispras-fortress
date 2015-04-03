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
  public void setSeed(int seed) {
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
    return ((long) next() << Integer.SIZE) | next();
  }

  //------------------------------------------------------------------------------------------------
  // Next Integer Methods
  //------------------------------------------------------------------------------------------------

  private int nextNonNegativeInt() {
    return (nextInt() & (-1 >>> 1));
  }

  private int nextNonNegativeIntLess(int max) {
    return nextNonNegativeInt() % max;
  }

  private int nextNonNegativeIntLessOrEqual(int max) {
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
  public int nextIntRange(int min, int max) {
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
  public int nextIntField(int width) {
    return next() & BitUtils.maskInt(width);
  }

  /**
   * Returns a number with the randomized range of bits (field).
   * 
   * @param lo the low bound of the field.
   * @param hi the high bound of the field.
   * @return a random number.
   */
  public int nextIntField(int lo, int hi) {
    return next() & BitUtils.maskInt(lo, hi);
  }

  //------------------------------------------------------------------------------------------------
  // Next Long Methods
  //------------------------------------------------------------------------------------------------

  private long nextNonNegativeLong() {
    return (nextLong() & (-1L >>> 1));
  }

  private long nextNonNegativeLongLess(long max) {
    return nextNonNegativeLong() % max;
  }

  private long nextNonNegativeLongLessOrEqual(long max) {
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
  public long nextLongRange(long min, long max) {
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
  public long nextLongField(int width) {
    return nextLong() & BitUtils.maskLong(width);
  }

  /**
   * Returns a number with the randomized range of bits (field).
   * 
   * @param lo the low bound of the field.
   * @param hi the high bound of the field.
   * @return a random number.
   */
  public long nextLongField(int lo, int hi) {
    return nextLong() & BitUtils.maskLong(lo, hi);
  }

  //------------------------------------------------------------------------------------------------
  // Next Big Integer Methods
  //------------------------------------------------------------------------------------------------

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

    if (diff.compareTo(BigInteger.valueOf(Long.MAX_VALUE)) > 0) {
      throw new IllegalArgumentException(String.format("(max-min)=%s is to too large", diff));
    }

    final long offset = nextLongRange(0, diff.longValue());

    return min.add(BigInteger.valueOf(offset));
  }

  //------------------------------------------------------------------------------------------------
  // Choose Methods
  //------------------------------------------------------------------------------------------------

  /**
   * Chooses a random item of the given array.
   * 
   * @param array the array whose items are chosen.
   * @return a random item of the array.
   * @throws NullPointerException if {@code array == null}.
   * @throws IllegalArgumentException if {@code array} is empty.
   */
  public <T> T choose(final T[] array) {
    InvariantChecks.checkNotEmpty(array);

    return array[nextIntRange(0, array.length - 1)];
  }

  /**
   * Chooses a random item of the given collection.
   * 
   * @param collection the collection whose items are chosen.
   * @return a random item of the collection.
   * @throws NullPointerException if {@code collection == null}.
   * @throws IllegalArgumentException if {@code collection} is empty.
   */
  public <T> T choose(final Collection<T> collection) {
    InvariantChecks.checkNotEmpty(collection);

    final ArrayList<T> arrayList = new ArrayList<>(collection);
    return arrayList.get(nextIntRange(0, collection.size() - 1));
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
