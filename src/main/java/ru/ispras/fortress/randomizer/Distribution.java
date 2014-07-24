/*
 * Copyright 2013 ISP RAS (http://www.ispras.ru)
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

/**
 * This class represents a discrete probability distribution.
 *
 * @author <a href="mailto:kamkin@ispras.ru">Alexander Kamkin</a>
 */
public final class Distribution
{
    private final int[] p;
    private final int[] v;

    /**
     * Constructs a probability distribution object.
     *
     * @param variants the values of the variate.
     * @param weights  the random biases of the values.
     * 
     * @throws NullPointerException if any of the parameters equals null.
     * @throws IllegalArgumentException if the variants and weights arrays
     * have different sizes or their size is 0; if the weights array contains
     * negative numbers.  
     */
    public Distribution(final int[] variants, final int[] weights)
    {
        notNullCheck(variants);
        notNullCheck(weights);

        if (0 == variants.length)
            throw new IllegalArgumentException();

        if (variants.length != weights.length)
            throw new IllegalArgumentException();

        this.p = new int[weights.length];
        this.v = new int[weights.length];

        int m = 0;
        for(int i = 0; i < weights.length; i++)
        {
            if (weights[i] < 0)
                throw new IllegalArgumentException(String.format(
                    "weights[%d]=%d is less than 0.", i, weights[i]));

            this.p[i] = (m += weights[i]);
            this.v[i] = variants[i];
        }
    }

    /**
    * Constructs a probability distribution object. A deduced form based on
    * the two-parameter constructor. The values are generated a a natural series.
    *
    * @param weights the random biases of the values.
    * 
    * @throws NullPointerException if the parameter equals null.
    * @throws IllegalArgumentException if weights array is empty 
    * (its size is 0; if the weights array contains negative numbers.
    */
    public Distribution(final int[] weights)
    {
        this(
            weights != null ? getNaturalSeries(weights.length) : null,
            weights
        );
    }

    public int getMaxWeight()
    {
        return p[p.length - 1];
    }

    public int getWeight(int variant)
    {
        return p[variant] - (variant != 0 ? p[variant - 1] : 0);
    }

    public void setWeight(int variant, int weight)
    {
        final int delta = weight - getWeight(variant);

        for(int i = variant; i < p.length; i++)
            { p[i] += delta; }
    }

    public int getLessOrEqualWeight(int variant)
    {
        return p[variant];
    }

    public int getVariant(int random_weight)
    {
        final int i = binarySearch(p, 0, p.length - 1, random_weight);
        return v[i];
    }

    /**
     * Finds the index <code>i</code> from <code>[a, b]</code> such that
     * <code>x[i-1] <= v && v < x[i]</code>.
     * Note that <code>x[-1]</code> is assumed to be zero.
     *
     * @return i such that <code>x[i-1] <= v && v < x[i]</code>.
     * @param x the ordered array of integer values.
     * @param a the low bound of the array indices.
     * @param b the high bound of the array indices.
     * @param v the value being searched.
     */
    private int binarySearch(int[] x, int a, int b, int v)
    {
        if(a == b)     return a;
        if(b == a + 1) return x[a] <= v ? b : a;
            
        final int i = (a + b) >> 1;
       
        if(x[i - 1] <= v && v < x[i])
            return i;

        if(v < x[i])
            return binarySearch(x, a, i - 1, v);
        else    
            return binarySearch(x, i + 1, b, v);
    }

    /**
     * Returns the natural series of the size <code>n</code> (0, 1, ... n-1).
     *
     * @param n the size of the series.
     * @return the natural series.
     */
    private static int[] getNaturalSeries(int n)
    {
        int[] result = new int[n];

        for(int i = 0; i < n; i++)
            result[i] = i;

        return result;
    }
    
    private void notNullCheck(Object o)
    {
        if (null == o)
            throw new NullPointerException();
    }
}
