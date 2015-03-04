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
import java.util.HashMap;
import java.util.Map;

import ru.ispras.fortress.util.InvariantChecks;

/**
 * This class represents an interval {@code T}-type random variate, where {@code T} is an integer
 * type ({@code Integer}, {@code Long} or {@code BigInteger}).
 * 
 * @author <a href="mailto:kamkin@ispras.ru">Alexander Kamkin</a>
 */
public final class VariateInterval<T extends Number & Comparable<T>> implements Variate<T> {

  /**
   * This enumeration contains supported types.
   */
  private static enum Type {
    INTEGER(Integer.class) {
      @Override <TT extends Number & Comparable<TT>> Object nextRange(TT min, TT max) {
        return Randomizer.get().nextIntRange(min.intValue(), max.intValue());
      }
    },

    LONG(Long.class) {
      @Override <TT extends Number & Comparable<TT>> Object nextRange(TT min, TT max) {
        return Randomizer.get().nextLongRange(min.longValue(), max.longValue());
      }
    },

    BIG_INTEGER(BigInteger.class) {
      @Override <TT extends Number & Comparable<TT>> Object nextRange(TT min, TT max) {
        return Randomizer.get().nextBigIntegerRange((BigInteger) min, (BigInteger) max);
      }
    };

    private static final Map<Class<?>, Type> types = new HashMap<>();
    static {
      for (Type type : values()) {
        types.put(type.typeClass, type);
      }
    }

    private final Class<?> typeClass;

    private Type(Class<?> typeClass) {
      this.typeClass = typeClass;
    }

    static Type fromClass(Class<?> typeClass) {
      return types.get(typeClass);
    }

    abstract <TT extends Number & Comparable<TT>> Object nextRange(TT min, TT max);
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
   * @throws NullPointerException if {@code min == null} or {@code max == null}.
   * @throws IllegalArgumentException (1) if min and max have different types,
   *         (2) if {@code min > max} or (3) if the value type is unsupported.
   */
  public VariateInterval(final T min, final T max) {
    InvariantChecks.checkNotNull(type);
    InvariantChecks.checkNotNull(min);
    InvariantChecks.checkNotNull(max);

    if (!min.getClass().equals(max.getClass())) {
      throw new IllegalArgumentException(String.format(
          "Different types for min and max: %s and %s.", 
          min.getClass().getName(), max.getClass().getName()));
    }

    InvariantChecks.checkGreaterOrEq(max, min);

    final Class<?> typeClass = min.getClass();

    final Type type = Type.fromClass(typeClass);
    if (null == type) {
      throw new IllegalArgumentException(String.format(
          "Type %s is not supported.", typeClass.getName()));
    }

    this.type = type;
    this.min = min;
    this.max = max;
  }

  @SuppressWarnings("unchecked")
  @Override
  public T value() {
    return (T) type.nextRange(min, max);
  }
}
