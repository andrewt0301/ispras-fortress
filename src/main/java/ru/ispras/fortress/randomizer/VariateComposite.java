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

import java.util.Collection;
import java.util.List;

/**
 * This class represents a composite {@code T}-type random variate.
 * 
 * @author <a href="mailto:kamkin@ispras.ru">Alexander Kamkin</a>
 */
public final class VariateComposite<T> implements Variate<T> {

  /** The composition of random variates (a random variate whose values are random variates). */
  private Variate<Variate<T>> composite;

  /**
   * Constructs a composite random variate.
   * 
   * @param variates the random variates to be composed.
   * @param biases the biases of the random variates.
   * 
   * @throws NullPointerException if {@code variates == null} or {@code biases == null}.
   * @throws IllegalArgumentException if the {@code variates} and {@code biases} arrays have
   *         different sizes or they are empty or the {@code biases} array contains negative
   *         numbers.
   */
  public VariateComposite(final Variate<T>[] variates, final int[] biases) {
    composite = new VariateBiased<Variate<T>>(variates, biases);
  }

  /**
   * Constructs a composite random variate.
   * 
   * @param variates the random variates to be composed.
   * @param biases the biases of the random variates.
   * 
   * @throws NullPointerException if {@code variates == null} or {@code biases == null}.
   * @throws IllegalArgumentException if the {@code variates} and {@code biases} arrays have
   *         different sizes or they are empty or the {@code biases} array contains negative
   *         numbers.
   */
  public VariateComposite(final List<Variate<T>> variates, final List<Integer> biases) {
    composite = new VariateBiased<Variate<T>>(variates, biases);
  }

  /**
   * Constructs a composite random variate.
   * 
   * @param variates the random variates to be composed.
   * 
   * @throws NullPointerException if {@code variates == null}.
   * @throws IllegalArgumentException if {@code variates} is empty.
   */
  public VariateComposite(final Variate<T>[] variates) {
    composite = new VariateCollection<Variate<T>>(variates);
  }

  /**
   * Constructs a composite random variate.
   * 
   * @param variates the random variates to be composed.
   * 
   * @throws NullPointerException if {@code variates == null}.
   * @throws IllegalArgumentException if {@code variates} is empty.
   */
  public VariateComposite(final Collection<Variate<T>> variates) {
    composite = new VariateCollection<Variate<T>>(variates);
  }

  @Override
  public T value() {
    final Variate<T> variate = composite.value();
    return variate.value();
  }
}
