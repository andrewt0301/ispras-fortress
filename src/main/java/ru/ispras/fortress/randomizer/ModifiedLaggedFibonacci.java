/*
 * Copyright 2013-2014 ISP RAS (http://www.ispras.ru)
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

/**
 * The modified additive lagged Fibonacci random number generator.
 * 
 * @author <a href="mailto:kamkin@ispras.ru">Alexander Kamkin</a>
 */
public final class ModifiedLaggedFibonacci implements RandomGenerator {
  // The algorithm uses two independent Fibonacci generators.
  private final LaggedFibonacci x;
  private final LaggedFibonacci y;

  /**
   * Constructs a modified additive lagged Fibonacci random number generator with the default (zero)
   * seed.
   */
  public ModifiedLaggedFibonacci() {
    this(0);
  }

  /**
   * Constructs a modified additive lagged Fibonacci random number generator with the given seed.
   * 
   * @param s the seed to be set.
   */
  public ModifiedLaggedFibonacci(final int s) {
    x = new LaggedFibonacci(s);
    y = new LaggedFibonacci(s + 1);
  }

  @Override
  public void seed(final int s) {
    // Two consequent seeds are used.
    x.seed(s);
    y.seed(s + 1);
  }

  @Override
  public int next() {
    // The further is to avoid bit correlations.
    return (x.next() & ~1) ^ (y.next() >> 1);
  }
}
