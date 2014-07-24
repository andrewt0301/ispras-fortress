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

import java.util.Arrays;

/**
 * The additive lagged Fibonacci random number generator.
 *
 * @author <a href="mailto:kamkin@ispras.ru">Alexander Kamkin</a>
 */
public final class LaggedFibonacci implements RandomGenerator
{
    private final static int J = 24;
    private final static int K = 55;
    
    private final static int SEED_MASK = 0xDEADBEAF;
    
    private int j = K - J;
    private int k = 0;
    
    private final int[] state = new int[K];    

    /**
     * Constructs an additive lagged Fibonacci random number generator with the
     * default (zero) seed.
     */
    public LaggedFibonacci()
    {
        seed(0);
    }
    
    /**
     * Constructs an additive lagged Fibonacci random number generator with the
     * given seed.
     *
     * @param s the seed to be set.
     */
    public LaggedFibonacci(int s)
    {
        seed(s);
    }

    @Override
    public void seed(int s)
    {
        int i, j, k;

        int[] b = new int[(Integer.SIZE - 1) * (K - 1)];

        Arrays.fill(state, 0);

        // See, e.g., Pat Burns's "Lagged, Fibonacci Random Number Generators":
        // l.s.b. of the 11th word should be 1.
        state[(K - 1) - 11] |= 1;

        s ^= SEED_MASK;

        for(i = 0; i < Integer.SIZE; i++)
            { b[i] = (s >> i) & 1; }

        // The initial state is filled with the bits generated by the Tausworthe
        // binary shift register (see, e.g., Pat Burns's article):
        // b[n] = (b[n-31] + b[n-6] + b[n-4] + b[n-2] + b[n-1]) (mod 2).
        for(i = 31; i < b.length; i++)
            { b[i] = (b[i-31] + b[i-6] + b[i-4] + b[i-2] + b[i-1]) & 1; }

        for(i = 0; i < b.length; i++)
        {
            j = (K - 1) - (i % (K - 1));
            k = i / (K - 1) + 1;

            if(b[i] != 0)
                { state[j] |= (1 << k); }
        } 
    }

    @Override
    public int next()
    {
        // x[n] = x[n-j] + x[n-k].
        final int x = state[j] + state[k];

        // LFG state is organized as a cyclic array.
        state[k] = x;

        if(++j == K) { j = 0; }
        if(++k == K) { k = 0; }

        return x;
    }
}