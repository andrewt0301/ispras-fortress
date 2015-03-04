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
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import ru.ispras.fortress.util.InvariantChecks;

/**
 * This class represents a finite-set {@code T}-type random variate.
 * 
 * @author <a href="mailto:kamkin@ispras.ru">Alexander Kamkin</a>
 */
public final class FiniteSetRandomVariate<T> implements RandomVariate<T> {

  /** The value area of the random variate. */
  private List<T> values;

  /**
   * Constructs a finite-set random variate.
   * 
   * @param values the value area of the random variate. 
   * @throws NullPointerException if {@code values == null}.
   * @throws IllegalArgumentException if {@code values} is empty.
   */
  public FiniteSetRandomVariate(final T[] values) {
    InvariantChecks.checkNotEmpty(values);

    this.values = Arrays.asList(values);
  }

  /**
   * Constructs a finite-set random variate.
   * 
   * @param values the value area of the random variate. 
   * @throws NullPointerException if {@code values == null}.
   * @throws IllegalArgumentException if {@code values} is empty.
   */
  public FiniteSetRandomVariate(final Collection<T> values) {
    InvariantChecks.checkNotEmpty(values);

    this.values = new ArrayList<>(values);
  }

  @Override
  public T value() {
    return values.get(Randomizer.get().nextIntRange(0, values.size() - 1));
  }
}
