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

import java.math.BigInteger;

import ru.ispras.fortress.util.InvariantChecks;

/**
 * This class represents an interval {@code T}-type random variate, where {@code T} is an integer
 * type ({@code Integer}, {@code Long} or {@code BigInteger}).
 * 
 * @author <a href="mailto:kamkin@ispras.ru">Alexander Kamkin</a>
 */
public final class VariateInterval<T extends Number & Comparable<T>>
    implements Variate<T> {

  /**
   * This enumeration contains supported types.
   */
  private static enum Type {
    INTEGER,
    LONG,
    BIG_INTEGER
  }

  /** The type information. */
  private Type type;

  /** The lower bound of the interval. */
  private T min;
  /** The upper bound of the interval. */
  private T max;

  /**
   * Constructs an interval random variate.
   * 
   * @param min the lower bound of the interval.
   * @param max the upper bound of the interval.
   *
   * @throws NullPointerException if {@code type == null}, {@code min == null} or
   *         {@code max == null}.
   * @throws IllegalArgumentException if {@code min > max} or type {@code T} is unsupported.
   */
  public VariateInterval(final Class<T> type, final T min, final T max) {
    InvariantChecks.checkNotNull(type);
    InvariantChecks.checkNotNull(min);
    InvariantChecks.checkNotNull(max);
    InvariantChecks.checkGreaterOrEq(max, min);

    if (type.equals(Integer.class)) {
      this.type = Type.INTEGER;
    } else if (type.equals(Long.class)) {
      this.type = Type.LONG;
    } else if (type.equals(BigInteger.class)) {
      this.type = Type.BIG_INTEGER;
    } else {
      throw new IllegalArgumentException(String.format("Type %s is unsupported", type));
    }

    this.min = min;
    this.max = max;
  }

  @SuppressWarnings("unchecked")
  @Override
  public T value() {
    switch (type) {
      case INTEGER:
        return (T) ((Integer) Randomizer.get().nextIntRange((Integer) min, (Integer) max));
      case LONG:
        return (T) ((Long) Randomizer.get().nextLongRange((Long) min, (Long) max));
      case BIG_INTEGER:
        return (T) (Randomizer.get().nextBigIntegerRange((BigInteger) min, (BigInteger) max));
      default:
        return null;
    }
  }
}
