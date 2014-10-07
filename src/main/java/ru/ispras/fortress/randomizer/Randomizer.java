/*
 * Copyright 2007-2013 ISP RAS (http://www.ispras.ru)
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package ru.ispras.fortress.randomizer;

import java.util.List;

import ru.ispras.fortress.data.types.bitvector.BitVector;
import ru.ispras.fortress.data.types.bitvector.BitVectorAlgorithm;

/**
 * This class is a wrapper around a random number generator. It is responsible
 * for generating random objects (numbers, strings, etc.) and filling storages
 * (arrays, collections, etc.) with random data.
 *
 * @author <a href="mailto:kamkin@ispras.ru">Alexander Kamkin</a>
 */
public final class Randomizer
{
    /**
     * Randomizer instance (singleton).
     */
    private static Randomizer randomizer = null;

    /**
     * Returns the randomizer instance.
     *
     * @return the randomizer instance.
     */
    public static Randomizer get()
    {
        if (null == randomizer)
            randomizer = new Randomizer();

        return randomizer;
    }

    /**
     * The random number generator used by the randomizer.
     */
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
    public RandomGenerator getGenerator()
    {
        return generator;
    }

    /**
     * Sets the current random number generator.
     *
     * @param generator the random number generator to be set.
     */
    public void setGenerator(final RandomGenerator generator)
    {
        this.generator = generator;
    }

    /**
     * Sets the new seed of the random number generator.
     *
     * @param seed the seed to be set.
     */
    public void setSeed(int seed)
    {
        generator.seed(seed);
    }

    /**
     * Generates the next random integer value.
     * 
     * @return the next random integer number.
     */
    public int next()
    {
        return generator.next();
    }

    /**
     * Returns a bit mask of the given width.
     * 
     * @param width Mask width.
     * @return Integer bit mask.
     */
    public int maskInt(int width)
    {
        return width >= Integer.SIZE ? -1 : (1 << width) - 1;
    }

    /**
     * Returns a bit mask for the given range.
     * 
     * @param lo Lower bound.
     * @param hi Higher bound. 
     * @return Integer bit mask.
     */
    public int maskInt(int lo, int hi)
    {
        int x = lo < hi ? lo : hi;
        int y = lo < hi ? hi : lo;

        if(y >= Integer.SIZE)
            y = Integer.SIZE - 1;

        return maskInt((y - x) + 1) << x;
    }

    /**
     * Returns a bit mask of the given width.
     * 
     * @param width Mask width.
     * @return Long bit mask.
     */
    public long maskLong(int width)
    {
        return width >= Long.SIZE ? -1 : (1 << width) - 1;
    }

    /**
     * Returns a bit mask for the given range.
     * 
     * @param lo Lower bound.
     * @param hi Higher bound. 
     * @return Long bit mask.
     */
    public long maskLong(int lo, int hi)
    {
        int x = lo < hi ? lo : hi;
        int y = lo < hi ? hi : lo;

        if(y >= Long.SIZE)
            y = Long.SIZE - 1;

        return maskLong((y - x) + 1) << x;
    }

    /**
     * Generates the next random byte.
     * 
     * @return A random byte.
     */
    public byte nextByte() { return (byte)next(); }

    /**
     * Generates the next random char.
     * 
     * @return A random char.
     */
    public char nextChar() { return (char)next(); }

    /**
     * Generates the next random int.
     * 
     * @return A random int.
     */
    public int nextInt() { return (int)next(); }

    /**
     * Generates the next random long.
     * 
     * @return A random long.
     */
    public long nextLong() { return ((long)next() << Integer.SIZE) | next(); }

    /**
     * Generates the next random boolean.
     * 
     * @return A random boolean.
     */
    public boolean nextBoolean() { return (next() & 1) != 0 ? true : false; }

    /**
     * Returns a random number from the given range.
     *
     * @return a random number.
     * @param min the low bound of the range.
     * @param max the high bound of the range.
     */
    public int nextIntRange(int min, int max)
    {
        if(min > max)
            throw new IllegalArgumentException("min is greater than max");

        int rnd = nextInt();

        if(max >= 0 && min >= max - Integer.MAX_VALUE || max < 0 && max <= Integer.MAX_VALUE + min)
            return min + rnd % ((max - min) + 1);

        if(rnd < min)
            return (rnd - Integer.MIN_VALUE) + min;

        if(rnd > max)
            return max - (Integer.MAX_VALUE - rnd);

        return rnd;
    }

    /**
     * Returns a random number of the given bit size (width).
     *
     * @return a random number.
     * @param width the bit size.
     */
    public int nextIntField(int width)
    {
        return next() & maskInt(width);
    }

    /**
     * Returns a number with the randomized range of bits (field).
     *
     * @return a random number.
     * @param lo the low bound of the field.
     * @param hi the high bound of the field.
     */
    public int nextIntField(int lo, int hi)
    {
        return next() & maskInt(lo, hi);
    }

    /**
     * Returns a random number from the given range.
     *
     * @return a random number.
     * @param min the low bound of the range.
     * @param max the high bound of the range.
     */
    public long nextLongRange(long min, long max)
    {
        if(min > max)
            throw new IllegalArgumentException("min is greater than max");

        long rnd = nextLong();

        if(max >= 0 && min >= max - Long.MAX_VALUE || max < 0 && max <= Long.MAX_VALUE + min)
            return min + rnd % ((max - min) + 1);

        if(rnd < min)
            return (rnd - Long.MIN_VALUE) + min;

        if(rnd > max)
            return max - (Long.MAX_VALUE - rnd);

        return rnd;
    }

    /**
     * Returns a random number of the given bit size (width).
     *
     * @return a random number.
     * @param width the bit size.
     */
    public long nextLongField(int width)
    {
        return nextLong() & maskLong(width);
    }

    /**
     * Returns a number with the randomized range of bits (field).
     *
     * @return a random number.
     * @param lo the low bound of the field.
     * @param hi the high bound of the field.
     */
    public long nextLongField(int lo, int hi)
    {
        return nextLong() & maskLong(lo, hi);
    }

    /**
     * Chooses a random item of the given array.
     *
     * @return a random item of the array.
     * @param array the array whoose items are chosen.
     */
    public <T> T choose(final T[] array)
    {
        return array[nextIntRange(0, array.length - 1)];
    }

    /**
     * Chooses a random item of the given list.
     *
     * @return a random item of the array.
     * @param list the list whose items are chosen.
     */
    public <T> T choose(final List<T> list)
    {
        return list.get(nextIntRange(0, list.size() - 1));
    }

    /**
     * Chooses a variant ([0, N-1]) according to the probability distribution.
     *
     * @return a randomly chosen variant.
     * @param biases the probability distribution.
     */
    public int choose(final Distribution biases)
    {
        return biases.getVariant(nextIntRange(0, biases.getMaxWeight() - 1));
    }

    /**
     * Fills the byte array with random data.
     *
     * @param data the array to be randomized.
     */
    public void fill(byte[] data)
    {
        for(int i = 0; i < data.length; i++)
            data[i] = nextByte();
    }

    /**
     * Fills the char array with random data.
     *
     * @param data the array to be randomized.
     */
    public void fill(char[] data)
    {
        for(int i = 0; i < data.length; i++)
            data[i] = nextChar();
    }

    /**
     * Fills the int array with random data.
     *
     * @param data the array to be randomized.
     */
    public void fill(int[] data)
    {
        for(int i = 0; i < data.length; i++)
            data[i] = nextInt();
    }

    /**
     * Fills the long array with random data.
     *
     * @param data the array to be randomized.
     */
    public void fill(long[] data)
    {
        for(int i = 0; i < data.length; i++)
            data[i] = nextLong();
    }

    /**
     * Fills the raw data storage with random data.
     *
     * @param data the raw data storage to be randomized.
     */
    public void fill(BitVector data)
    {
        BitVectorAlgorithm.generate(data, new BitVectorAlgorithm.IOperation()
        {
            @Override public byte run() { return nextByte(); }
        });
    }
}
