/*
 * Copyright 2014-2015 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.util;

import java.util.Collection;

/**
 * The InvariantChecks class provides static methods for checking different kinds
 * of invariants. If a check fails a corresponding exception is thrown.
 * 
 * @author Andrei Tatarnikov
 */

public final class InvariantChecks {
  private InvariantChecks() {}

  /**
   * Checks the invariant "Condition is true" and throws an exception
   * if it is violated.
   * 
   * @param condition Condition to be checked.
   * 
   * @throws IllegalArgumentException if the invariant is violated
   * ({@code condition} is {@code false}).
   */

  public static void checkTrue(final boolean condition) {
    if (!condition) {
      throw new IllegalArgumentException();
    }
  }

  /**
   * Checks the invariant "Condition is false" and throws an exception
   * if it is violated.
   * 
   * @param condition Condition to be checked.
   * 
   * @throws IllegalArgumentException if the invariant is violated
   * ({@code condition} is {@code true}).
   */

  public static void checkFalse(final boolean condition) {
    checkTrue(!condition);
  }

  /**
   * Checks the invariant "Object reference is not null" and
   * throws an exception if it is violated. 
   * 
   * @param o Object reference to be checked.
   * 
   * @throws IllegalArgumentException if the invariant is violated ({@code o} is {@code null}).
   */

  public static <T> void checkNotNull(final T o) {
    checkTrue(null != o);
  }

  /**
   * Checks the invariants "Object reference is not null" and "Collection is not empty"
   * throws an exception if they are violated. 
   * 
   * @param o Collection to be checked.
   * 
   * @throws IllegalArgumentException if the invariant is violated ({@code o} is {@code null});
   *         if the invariant is violated ({@code o.isEmpty}).
   */

  public static <T> void checkNotEmpty(final Collection<T> o) {
    checkNotNull(o);

    if (o.isEmpty()) {
      throw new IllegalArgumentException(String.format("%s must not be empty", o));
    }
  }

  /**
   * Checks the invariants "Object reference is not null" and "Array is not empty"
   * throws an exception if they are violated. 
   * 
   * @param o Array to be checked.
   * 
   * @throws IllegalArgumentException if the invariant is violated ({@code o} is {@code null});
   *         if the invariant is violated ({@code o.length} is 0).
   */

  public static <T> void checkNotEmpty(final T[] o) {
    checkNotNull(o);

    if (o.length == 0) {
      throw new IllegalArgumentException(String.format("%s must not be empty", o));
    }
  }

  /**
   * Checks the invariant "Integer value is greater than {@code 0}" and
   * throws an exception if it is violated. 
   * 
   * @param n Integer value to be checked.
   * 
   * @throws IllegalArgumentException if the invariant is violated ({@code n} <= {@code 0}).
   */

  public static void checkGreaterThanZero(final int n) {
    if (n <= 0) {
      throw new IllegalArgumentException(
          String.format("%d must be > 0", n));
    }
  }

  /**
   * Checks the invariant "Integer value is greater or equal {@code 0}" and
   * throws an exception if it is violated. 
   * 
   * @param n Integer value to be checked.
   * 
   * @throws IllegalArgumentException if the invariant is violated ({@code n} < {@code 0}).
   */

  public static void checkGreaterOrEqZero(final int n) {
    if (n < 0) {
      throw new IllegalArgumentException(
          String.format("%d must be >= 0", n));
    }
  }

  /**
   * Checks the invariant "{@code 0 <= index < length}" and
   * throws an exception if it is violated. 
   * 
   * @param index Index to be checked.
   * @param length Length of the allowed range.
   * 
   * @throws IndexOutOfBoundsException if the invariant is violated
   * ({@code index} is not within range {@code [0..length)}).
   */

  public static void checkBounds(final int index, final int length) {
    if (!(0 <= index && index < length)) {
      throw new IndexOutOfBoundsException(String.format(
          "%d must be within range [0, %d)", index, length));
    }
  }

  /**
   * Checks the invariant "{@code 0 <= index <= length}" and
   * throws an exception if it is violated. 
   * 
   * @param index Index to be checked.
   * @param length Length of the allowed range.
   * 
   * @throws IndexOutOfBoundsException if the invariant is violated
   * ({@code index} is not within range {@code [0..length]}).
   */

  public static void checkBoundsInclusive(final int index, final int length) {
    if (!(0 <= index && index <= length)) {
      throw new IndexOutOfBoundsException(String.format(
          "%d must be within range [0, %d]", index, length));
    }
  }

  /**
   * Checks the invariant "Numeric value {@code a} is greater than {@code b}" and
   * throws an exception if it is violated. 
   * 
   * @param a Numeric value to be checked.
   * @param b Numeric value to be checked.
   * 
   * @throws IllegalArgumentException if the invariant is violated ({@code a <= b}).
   */

  public static <T extends Number & Comparable<T>> void checkGreaterThan(final T a, final T b) {
    if (a.compareTo(b) <= 0) {
      throw new IllegalArgumentException(
          String.format("%s must be > %s", a, b));
    }
  }

  /**
   * Checks the invariant "Numeric value {@code a} is greater than or equal to {@code b}" and
   * throws an exception if it is violated. 
   * 
   * @param a Numeric value to be checked.
   * @param b Numeric value to be checked.
   * 
   * @throws IllegalArgumentException if the invariant is violated ({@code a < b}).
   */

  public static <T extends Number & Comparable<T>> void checkGreaterOrEq(final T a, final T b) {
    if (a.compareTo(b) < 0) {
      throw new IllegalArgumentException(
          String.format("%s must be >= %s", a, b));
    }
  }
}
