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

/**
 * This class represents a single-value {@code T}-type random variate.
 * 
 * @param <T> the type of the random variate values.
 * 
 * @author <a href="mailto:kamkin@ispras.ru">Alexander Kamkin</a>
 */
public final class VariateSingleValue<T> implements Variate<T> {

  /** The single value. */
  private T value;

  /**
   * Constructs a single-value random variate.
   * 
   * @param value the value of the random variate. 
   */
  public VariateSingleValue(final T value) {
    this.value = value;
  }

  @Override
  public T value() {
    return value;
  }
}
