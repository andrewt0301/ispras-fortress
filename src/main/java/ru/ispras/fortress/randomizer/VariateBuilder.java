/*
 * Copyright 2015 ISP RAS (http://www.ispras.ru)
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

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import ru.ispras.fortress.util.InvariantChecks;

/**
 * This class implements a probability distribution builder for a {@code T}-type random variate.
 * 
 * @param <T> the type of the random variate values. 
 * 
 * @author <a href="mailto:kamkin@ispras.ru">Alexander Kamkin</a>
 */
public final class VariateBuilder<T> {

  /** The special constant designating the default bias. */ 
  private static final int DEFAULT_BIAS = Integer.MAX_VALUE;

  /** The random variates. */
  private final List<Variate<T>> values = new ArrayList<>();
  /** The random biases. */
  private final List<Integer> biases = new ArrayList<>();

  /**
   * Adds the random variate with the given bias.
   * 
   * @param variate the random variate to be added.
   * @param bias the bias of the random variate.
   * @throws IllegalArgumentException if {@code variate == null}; if {@code bias <= 0}.
   */
  public void addVariate(final Variate<T> variate, final int bias) {
    InvariantChecks.checkNotNull(variate);
    InvariantChecks.checkGreaterThanZero(bias);

    values.add(variate);
    biases.add(bias);
  }

  /**
   * Adds the random variate with the default bias.
   * 
   * @param variate the random variate to be added.
   * @throws NullPointerException if {@code variate == null}.
   */
  public void addVariate(final Variate<T> variate) {
    addVariate(variate, DEFAULT_BIAS);
  }

  /**
   * Adds the value with the given bias.
   * 
   * @param value the value to be added.
   * @param bias the bias of the value.
   * @throws IllegalArgumentException if {@code bias <= 0}.
   */
  public void addValue(final T value, final int bias) {
    InvariantChecks.checkGreaterThanZero(bias);

    addVariate(new VariateSingleValue<T>(value), bias);
  }

  /**
   * Adds the value with the default bias.
   * 
   * @param value the value to be added.
   */
  public void addValue(final T value) {
    addValue(value, DEFAULT_BIAS);
  }

  /**
   * Adds an interval with the given bias.
   * 
   * @param min the lower bound of the interval.
   * @param max the upper bound of the interval.
   * 
   * @throws IllegalArgumentException if {@code min} or {@code max} is {@code null}; 
   *         if {@code bias <= 0}.
   */
  public void addInterval(final T min, final T max, final int bias) {
    InvariantChecks.checkNotNull(min);
    InvariantChecks.checkNotNull(max);
    InvariantChecks.checkGreaterThanZero(bias);

    addVariate(new VariateInterval<T>(min, max), bias);
  }

  /**
   * Adds an interval with the default bias.
   * 
   * @param min the lower bound of the interval.
   * @param max the upper bound of the interval.
   */
  public void addInterval(final T min, final T max) {
    addInterval(min, max, DEFAULT_BIAS);
  }

  /**
   * Adds the array of values with the given bias.
   * 
   * @param values the values to be added.
   * @param bias the bias of the values.
   * @throws IllegalArgumentException if {@code values == null}; if {@code bias <= 0}.
   */
  public void addArray(final T[] values, final int bias) {
    InvariantChecks.checkNotNull(values);
    InvariantChecks.checkGreaterThanZero(bias);

    addVariate(new VariateCollection<T>(values), bias);
  }

  /**
   * Adds the array of values with the default bias.
   * 
   * @param values the values to be added.
   * @throws NullPointerException if {@code values == null}.
   */
  public void addArray(final T[] values) {
    addArray(values, DEFAULT_BIAS);
  }

  /**
   * Adds the collection of values with the given bias.
   * 
   * @param values the values to be added.
   * @param bias the bias of the values.
   * @throws IllegalArgumentException if {@code values == null}; if {@code bias <= 0}.
   */
  public void addCollection(final Collection<T> values, final int bias) {
    InvariantChecks.checkNotNull(values);
    InvariantChecks.checkGreaterThanZero(bias);

    addVariate(new VariateCollection<T>(values), bias);
  }

  /**
   * Adds the collection of values with the default bias.
   * 
   * @param values the values to be added.
   * @throws NullPointerException if {@code values == null}.
   */
  public void addCollection(final Collection<T> values) {
    addCollection(values, DEFAULT_BIAS);
  }

  /**
   * Constructs a random variate.
   * 
   * @return the constructed random variate.
   * @throws IllegalArgumentException if no values have been added.
   */
  public Variate<T> build() {
    InvariantChecks.checkNotEmpty(values);
    InvariantChecks.checkNotEmpty(biases);

    // The default bias = the minimal bias.
    int minBias = Integer.MAX_VALUE;

    for (final int bias : biases) {
      if (bias < minBias) {
        minBias = bias;
      }
    }

    if (minBias == Integer.MAX_VALUE) {
      return new VariateComposite<T>(values);
    }

    for (int i = 0; i < biases.size(); i++) {
      if (biases.get(i) == DEFAULT_BIAS) {
        biases.set(i, minBias);
      }
    }

    return new VariateComposite<T>(values, biases);
  }
}
