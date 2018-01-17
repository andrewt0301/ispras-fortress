/*
 * Copyright 2013-2018 ISP RAS (http://www.ispras.ru)
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

import ru.ispras.fortress.util.InvariantChecks;

import java.util.AbstractList;
import java.util.Arrays;
import java.util.List;

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
   * @throws IllegalArgumentException if {@code values == null} or {@code biases == null};
   *         if the {@code values} and {@code biases} arrays have different sizes
   *         or they are empty or the {@code biases} array contains negative numbers.
   */
  public VariateBiased(final List<T> values, final List<Integer> biases) {
    InvariantChecks.checkNotNull(values);
    InvariantChecks.checkNotEmpty(values);
    InvariantChecks.checkNotNull(biases);
    InvariantChecks.checkTrue(values.size() == biases.size(), String.format(
        "values.size()=%d is not equal to biases.size()=%d", values.size(), biases.size()));

    this.values = values;
    this.biasSums = new int[biases.size()];

    int biasSum = 0;

    for (int i = 0; i < biases.size(); i++) {
      final int bias = biases.get(i);
      InvariantChecks.checkTrue(bias >= 0, String.format(
          "biases[%d]=%d is less than 0.", i, bias));

      this.biasSums[i] = (biasSum += bias);
    }

    InvariantChecks.checkTrue(biasSum > 0);
  }

  /**
   * Constructs a biased random variate.
   * 
   * @param values the value area of the random variate.
   * @param biases the random biases of the values.
   * 
   * @throws IllegalArgumentException if {@code values == null} or {@code biases == null};
   *         if the {@code values} and {@code biases} arrays have different sizes
   *         or they are empty or the {@code biases} array contains negative numbers.
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
   * Finds an index {@code index} from {@code [low, high]} such that
   * {@code array[index-1] <= value && value < array[index]}.
   * {@code array[-1]} is assumed to be zero.
   * 
   * @param array the ordered array of integer values.
   * @param low the lower bound of the array indices.
   * @param high the upper bound of the array indices.
   * @param value the value being searched.
   * @return an index {@code index} such that
   *        {@code array[index-1] <= value && value < array[index]}.
   */
  private static int binarySearch(
      final int[] array,
      final int low,
      final int high,
      final int value) {
    if (low == high) {
      return low;
    }

    if (high == low + 1) {
      return array[low] <= value ? high : low;
    }

    final int index = (low + high) >> 1;

    if (array[index - 1] <= value && value < array[index]) {
      return index;
    }

    return value < array[index]
        ? binarySearch(array, low, index - 1, value)
        : binarySearch(array, index + 1, high, value);
  }
}
