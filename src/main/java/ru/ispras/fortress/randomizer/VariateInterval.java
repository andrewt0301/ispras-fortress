/*
 * Copyright 2015-2017 ISP RAS (http://www.ispras.ru)
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

import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;

/**
 * This class represents an interval {@code T}-type random variate, where {@code T} is an integer
 * type ({@code Integer}, {@code Long} or {@code BigInteger}).
 * 
 * @param <T> the type of the random variate values. 
 * 
 * @author <a href="mailto:kamkin@ispras.ru">Alexander Kamkin</a>
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public final class VariateInterval<T> implements Variate<T> {

  /**
   * This enumeration contains supported types.
   */
  private static enum Type {
    INTEGER(Integer.class) {
      @Override <TT> boolean isLessOrEq(final TT lhs, final TT rhs) {
        return (Integer) lhs <= (Integer) rhs;
      }

      @Override <TT> Object next(final TT min, final TT max) {
        return Randomizer.get().nextIntRange((Integer) min, (Integer) max);
      }
    },

    LONG(Long.class) {
      @Override <TT> boolean isLessOrEq(final TT lhs, final TT rhs) {
        return (Long) lhs <= (Long) rhs;
      }

      @Override <TT> Object next(final TT min, final TT max) {
        return Randomizer.get().nextLongRange((Long) min, (Long) max);
      }
    },

    BIG_INTEGER(BigInteger.class) {
      @Override <TT> boolean isLessOrEq(final TT lhs, final TT rhs) {
        return ((BigInteger) lhs).compareTo((BigInteger) rhs) <= 0;
      }

      @Override <TT> Object next(final TT min, final TT max) {
        return Randomizer.get().nextBigIntegerRange((BigInteger) min, (BigInteger) max);
      }
    };

    private static final Map<Class<?>, Type> TYPES = new HashMap<>();
    static {
      for (final Type type : values()) {
        TYPES.put(type.typeClass, type);
      }
    }

    private final Class<?> typeClass;

    private Type(final Class<?> typeClass) {
      this.typeClass = typeClass;
    }

    static Type fromClass(final Class<?> typeClass) {
      return TYPES.get(typeClass);
    }

    /**
     * Checks whether {@code lhs} is less than or equal to {@code rhs}.
     * 
     * @param lhs the left-hand-side operand.
     * @param rhs the right-hand-side operand.
     * @return {@code true} if {@code lhs <= rhs}; {@code false} otherwise.
     */
    abstract <TT> boolean isLessOrEq(final TT lhs, final TT rhs);

    /**
     * Choose a random number from the specified range.
     * 
     * @param min the lower bound of the range.
     * @param max the upper bound of the range.
     * @return a random number from {@code [min, max]}.
     */
    abstract <TT> Object next(final TT min, final TT max);
  }

  /** The type information. */
  private final Type type;

  /** The lower bound of the interval. */
  private final T min;
  /** The upper bound of the interval. */
  private final T max;

  /**
   * Constructs an interval random variate.
   * 
   * @param min the lower bound of the interval.
   * @param max the upper bound of the interval.
   * 
   * @throws IllegalArgumentException (1) if {@code min == null} or {@code max == null};
   *         (2) if min and max have incompatible types;
   *         (3) if {@code min > max};
   *         (4) if the value type is unsupported.
   */
  public VariateInterval(final T min, final T max) {
    this(min, max, getCastClass(min, max));
  }

  private VariateInterval(final T min, final T max, final Class<?> typeClass) {
    InvariantChecks.checkNotNull(min);
    InvariantChecks.checkNotNull(max);
    InvariantChecks.checkNotNull(typeClass);

    final Type type = Type.fromClass(typeClass);
    if (null == type) {
      throw new IllegalArgumentException(String.format(
          "Type %s is not supported.", typeClass.getName()));
    }

    this.type = type;
    this.min = cast(min, typeClass);
    this.max = cast(max, typeClass);

    if (!type.isLessOrEq(this.min, this.max)) {
      throw new IllegalArgumentException(String.format("%s must be <= %s", min, max));
    }
  }

  private static <T> Class<?> getCastClass(final T first, final T second) {
    InvariantChecks.checkNotNull(first);
    InvariantChecks.checkNotNull(second);

    if (first.getClass().equals(second.getClass())) {
      return first.getClass();
    }

    checkNumber(first);
    checkNumber(second);

    if (first instanceof BigInteger || second instanceof BigInteger) {
      return BigInteger.class;
    }

    if (first instanceof Long || second instanceof Long) {
      return Long.class;
    }

    if (first instanceof Integer || second instanceof Integer) {
      return Integer.class;
    }

    throw new IllegalArgumentException(String.format(
        "Unsupported or incompatible types: %s(%s) and %s(%s).",
        first, first.getClass().getName(), second, second.getClass().getName())
        );
  }

  private static void checkNumber(final Object value) {
    if (!(value instanceof Number)) {
      throw new IllegalArgumentException(
          String.format("%s(%s) is not a number.", value, value.getClass().getName()));
    }
  }

  @SuppressWarnings("unchecked")
  private static <T> T cast(final T value, Class<?> typeClass) {
    if (typeClass.equals(value.getClass())) {
      return value;
    }

    final Number number = (Number) value;
    final Number result;

    if (typeClass.equals(BigInteger.class)) {
      result = BigInteger.valueOf(number.longValue());
    } else if (typeClass.equals(Long.class)) {
      result = number.longValue();
    } else if (typeClass.equals(Integer.class)) {
      result = number.intValue();
    } else {
      throw new IllegalArgumentException("Unsupported type: " + typeClass.getSimpleName());
    }

    return (T) result;
  }

  @SuppressWarnings("unchecked")
  @Override
  public T value() {
    return (T) type.next(min, max);
  }
}
