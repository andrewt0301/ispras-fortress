/*
 * Copyright 2007-2014 ISP RAS (http://www.ispras.ru)
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

import java.util.List;

import ru.ispras.fortress.data.types.bitvector.BitVector;
import ru.ispras.fortress.data.types.bitvector.BitVectorAlgorithm;
import ru.ispras.fortress.util.BitUtils;

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
  private Randomizer() {}

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

  // ------------------------------------------------------------------------------------------------
  // Next Methods (Random Number Generators for Different Integer Types)
  // ------------------------------------------------------------------------------------------------

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

  // ------------------------------------------------------------------------------------------------
  // Next Integer Methods
  // ------------------------------------------------------------------------------------------------

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
   * Returns a random number from the given range.
   * 
   * @return a random number.
   * @param min the low bound of the range.
   * @param max the high bound of the range.
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
   * @return a random number.
   * @param width the bit size.
   */
  public int nextIntField(int width) {
    return next() & BitUtils.maskInt(width);
  }

  /**
   * Returns a number with the randomized range of bits (field).
   * 
   * @return a random number.
   * @param lo the low bound of the field.
   * @param hi the high bound of the field.
   */
  public int nextIntField(int lo, int hi) {
    return next() & BitUtils.maskInt(lo, hi);
  }

  // ------------------------------------------------------------------------------------------------
  // Next Long Methods
  // ------------------------------------------------------------------------------------------------

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
   * @return a random number.
   * @param min the low bound of the range.
   * @param max the high bound of the range.
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
   * @return a random number.
   * @param width the bit size.
   */
  public long nextLongField(int width) {
    return nextLong() & BitUtils.maskLong(width);
  }

  /**
   * Returns a number with the randomized range of bits (field).
   * 
   * @return a random number.
   * @param lo the low bound of the field.
   * @param hi the high bound of the field.
   */
  public long nextLongField(int lo, int hi) {
    return nextLong() & BitUtils.maskLong(lo, hi);
  }

  // ------------------------------------------------------------------------------------------------
  // Choose Methods
  // ------------------------------------------------------------------------------------------------

  /**
   * Chooses a random item of the given array.
   * 
   * @return a random item of the array.
   * @param array the array whoose items are chosen.
   */
  public <T> T choose(final T[] array) {
    return array[nextIntRange(0, array.length - 1)];
  }

  /**
   * Chooses a random item of the given list.
   * 
   * @return a random item of the array.
   * @param list the list whose items are chosen.
   */
  public <T> T choose(final List<T> list) {
    return list.get(nextIntRange(0, list.size() - 1));
  }

  /**
   * Chooses a variant ([0, N-1]) according to the probability distribution.
   * 
   * @return a randomly chosen variant.
   * @param biases the probability distribution.
   */
  public int choose(final Distribution biases) {
    return biases.getVariant(nextIntRange(0, biases.getMaxWeight() - 1));
  }

  // ------------------------------------------------------------------------------------------------
  // Fill Methods
  // ------------------------------------------------------------------------------------------------

  /**
   * Fills the byte array with random data.
   * 
   * @param data the array to be randomized.
   */
  public void fill(byte[] data) {
    for (int i = 0; i < data.length; i++) {
      data[i] = nextByte();
    }
  }

  /**
   * Fills the char array with random data.
   * 
   * @param data the array to be randomized.
   */
  public void fill(char[] data) {
    for (int i = 0; i < data.length; i++) {
      data[i] = nextChar();
    }
  }

  /**
   * Fills the int array with random data.
   * 
   * @param data the array to be randomized.
   */
  public void fill(int[] data) {
    for (int i = 0; i < data.length; i++) {
      data[i] = nextInt();
    }
  }

  /**
   * Fills the long array with random data.
   * 
   * @param data the array to be randomized.
   */
  public void fill(long[] data) {
    for (int i = 0; i < data.length; i++) {
      data[i] = nextLong();
    }
  }

  /**
   * Fills the raw data storage with random data.
   * 
   * @param data the raw data storage to be randomized.
   */
  public void fill(BitVector data) {
    BitVectorAlgorithm.generate(data, new BitVectorAlgorithm.IOperation() {
      @Override
      public byte run() {
        return nextByte();
      }
    });
  }
}
