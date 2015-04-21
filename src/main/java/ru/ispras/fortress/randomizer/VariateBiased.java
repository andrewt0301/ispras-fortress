/*
 * Copyright 2013-2015 ISP RAS (http://www.ispras.ru)
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

import java.util.AbstractList;
import java.util.Arrays;
import java.util.List;

import ru.ispras.fortress.util.InvariantChecks;

/**
 * This class represents a biased {@code T}-type random variate (a discrete probability
 * distribution).
 * 
 * @param <T> the type of the random variate values. 
 * 
 * @author <a href="mailto:kamkin@ispras.ru">Alexander Kamkin</a>
 */
public final class VariateBiased<T> implements Variate<T> {

  /** The value area of the random variate. */
  private final List<T> values;

  /**
   * The less-than-or-equal-to biases: {@code lessThanOrEqualToBiases[i]} is a bias of the
   * situation in which a random index is less than or equal to {@code i}.
   */
  private final int[] biasSums;

  /**
   * Constructs a biased random variate.
   * 
   * @param values the value area of the random variate.
   * @param biases the random biases of the values.
   * 
   * @throws NullPointerException if {@code values == null} or {@code biases == null}.
   * @throws IllegalArgumentException if the {@code values} and {@code biases} arrays have different
   *         sizes or they are empty or the {@code biases} array contains negative numbers.
   */
  public VariateBiased(final List<T> values, final List<Integer> biases) {
    InvariantChecks.checkNotEmpty(values);
    InvariantChecks.checkNotNull(biases);

    if (values.size() != biases.size()) {
      throw new IllegalArgumentException(String.format(
          "values.size()=%d is not equal to biases.size()=%d", values.size(), biases.size()));
    }

    this.values = values;
    this.biasSums = new int[biases.size()];

    int biasSum = 0;

    for (int i = 0; i < biases.size(); i++) {
      final int bias = biases.get(i);

      if (bias < 0) {
        throw new IllegalArgumentException(String.format(
            "biases[%d]=%d is less than 0.", i, bias));
      }

      this.biasSums[i] = (biasSum += bias);
    }
  }

  /**
   * Constructs a biased random variate.
   * 
   * @param values the value area of the random variate.
   * @param biases the random biases of the values.
   * 
   * @throws NullPointerException if {@code values == null} or {@code biases == null}.
   * @throws IllegalArgumentException if the {@code values} and {@code biases} arrays have different
   *         sizes or they are empty or the {@code biases} array contains negative numbers.
   */
  public VariateBiased(final T[] values, final int[] biases) {
    this(Arrays.asList(values), new AbstractList<Integer>() {
      @Override
      public Integer get(final int i) {
        return biases[i];
      }
      @Override
      public int size() {
        return biases.length;
      }
    });
  }

  @Override
  public T value() {
    final int bias = Randomizer.get().nextIntRange(0, biasSums[biasSums.length - 1] - 1);
    final int index = binarySearch(biasSums, 0, biasSums.length - 1, bias);

    return values.get(index);
  }

  /**
   * Finds an index {@code i} from {@code [a, b]} such that {@code x[i-1] <= v && v < x[i]}.
   * {@code x[-1]} is assumed to be zero.
   * 
   * @param x the ordered array of integer values.
   * @param a the lower bound of the array indices.
   * @param b the upper bound of the array indices.
   * @param v the value being searched.
   * @return an index {@code i} such that {@code x[i-1] <= v && v < x[i]}.
   */
  private static int binarySearch(final int[] x, final int a, final int b, final int v) {
    if (a == b) {
      return a;
    }

    if (b == a + 1) {
      return x[a] <= v ? b : a;
    }

    final int i = (a + b) >> 1;

    if (x[i - 1] <= v && v < x[i]) {
      return i;
    }

    return v < x[i] ? binarySearch(x, a, i - 1, v) : binarySearch(x, i + 1, b, v);
  }
}
