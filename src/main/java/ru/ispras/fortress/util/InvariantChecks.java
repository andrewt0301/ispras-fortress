/*
 * Copyright 2014-2018 ISP RAS (http://www.ispras.ru)
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
 * The {@code InvariantChecks} class provides static methods for checking different
 * kinds of invariants. If a check fails a corresponding exception is thrown.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
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
   *         ({@code condition} is {@code false}).
   */
  public static void checkTrue(final boolean condition) {
    checkTrue(condition, null);
  }

  /**
   * Checks the invariant "Condition is true" and throws an exception
   * if it is violated.
   *
   * @param condition Condition to be checked.
   * @param message Exception message.
   *
   * @throws IllegalArgumentException if the invariant is violated
   *         ({@code condition} is {@code false}).
   */
  public static void checkTrue(final boolean condition, final String message) {
    if (!condition) {
      throw message != null ? new IllegalArgumentException(message) :
                              new IllegalArgumentException();
    }
  }

  /**
   * Checks the invariant "Condition is false" and throws an exception
   * if it is violated.
   *
   * @param condition Condition to be checked.
   *
   * @throws IllegalArgumentException if the invariant is violated
   *         ({@code condition} is {@code true}).
   */
  public static void checkFalse(final boolean condition) {
    checkTrue(!condition);
  }

  /**
   * Checks the invariant "Condition is false" and throws an exception
   * if it is violated.
   *
   * @param condition Condition to be checked.
   * @param message Exception message.
   *
   * @throws IllegalArgumentException if the invariant is violated
   *         ({@code condition} is {@code true}).
   */
  public static void checkFalse(final boolean condition, final String message) {
    checkTrue(!condition, message);
  }

  /**
   * Checks the invariant "Object reference is not null" and
   * throws an exception if it is violated.
   *
   * @param objType Object reference to be checked.
   * @param <T> Object type.
   *
   * @throws IllegalArgumentException if the invariant is violated ({@code o} is {@code null}).
   */
  public static <T> void checkNotNull(final T objType) {
    checkTrue(null != objType);
  }

  /**
   * Checks the invariant "Object reference is not null" and
   * throws an exception if it is violated.
   *
   * @param obj Object reference to be checked.
   * @param message Exception message.
   * @param <T> Object type.
   *
   * @throws IllegalArgumentException if the invariant is violated ({@code o} is {@code null}).
   */
  public static <T> void checkNotNull(final T obj, final String message) {
    checkTrue(null != obj, message);
  }

  /**
   * Checks the invariants "Object reference is not null" and "Collection is not empty"
   * throws an exception if they are violated.
   *
   * @param collection Collection to be checked.
   * @param <T> Collection item type.
   *
   * @throws IllegalArgumentException if the invariant is violated ({@code o} is {@code null});
   *         if the invariant is violated ({@code o.isEmpty}).
   */
  public static <T> void checkNotEmpty(final Collection<T> collection) {
    checkNotNull(collection);

    if (collection.isEmpty()) {
      throw new IllegalArgumentException(String.format("%s must not be empty", collection));
    }
  }

  /**
   * Checks the invariants "Object reference is not null" and "Array is not empty"
   * throws an exception if they are violated.
   *
   * @param array Array to be checked.
   * @param <T> Array element type.
   *
   * @throws IllegalArgumentException if the invariant is violated ({@code o} is {@code null});
   *         if the invariant is violated ({@code o.length} is 0).
   */
  public static <T> void checkNotEmpty(final T[] array) {
    checkNotNull(array);

    if (array.length == 0) {
      throw new IllegalArgumentException(String.format("%s must not be empty", array));
    }
  }

  /**
   * Checks the invariant "Integer value is greater than {@code 0}" and
   * throws an exception if it is violated.
   *
   * @param num Integer value to be checked.
   *
   * @throws IllegalArgumentException if the invariant is violated ({@code n <= 0}).
   */
  public static void checkGreaterThanZero(final int num) {
    if (num <= 0) {
      throw new IllegalArgumentException(
          String.format("%d must be > 0", num));
    }
  }

  /**
   * Checks the invariant "Integer value is greater or equal {@code 0}" and
   * throws an exception if it is violated.
   *
   * @param num Integer value to be checked.
   *
   * @throws IllegalArgumentException if the invariant is violated ({@code n < 0}).
   */
  public static void checkGreaterOrEqZero(final int num) {
    if (num < 0) {
      throw new IllegalArgumentException(
          String.format("%d must be >= 0", num));
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
   *         ({@code index} is not within range {@code [0..length)}).
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
   *         ({@code index} is not within range {@code [0..length]}).
   */
  public static void checkBoundsInclusive(final int index, final int length) {
    if (!(0 <= index && index <= length)) {
      throw new IndexOutOfBoundsException(String.format(
          "%d must be within range [0, %d]", index, length));
    }
  }

  /**
   * Checks the invariant "Numeric value {@code first} is greater than {@code second}"
   * and throws an exception if it is violated.
   *
   * @param first Numeric value to be checked.
   * @param second Numeric value to be checked.
   * @param <T> Value type.
   *
   * @throws IllegalArgumentException if the invariant is violated ({@code a <= b}).
   */
  public static <T extends Number & Comparable<T>> void checkGreaterThan(
      final T first,
      final T second) {
    if (first.compareTo(second) <= 0) {
      throw new IllegalArgumentException(
          String.format("%s must be > %s", first, second));
    }
  }

  /**
   * Checks the invariant "Numeric value {@code first} is greater than or equal to {@code second}"
   * and throws an exception if it is violated.
   *
   * @param first Numeric value to be checked.
   * @param second Numeric value to be checked.
   * @param <T> Value type.
   *
   * @throws IllegalArgumentException if the invariant is violated ({@code a < b}).
   */
  public static <T extends Number & Comparable<T>> void checkGreaterOrEq(
      final T first,
      final T second) {
    if (first.compareTo(second) < 0) {
      throw new IllegalArgumentException(
          String.format("%s must be >= %s", first, second));
    }
  }
}
