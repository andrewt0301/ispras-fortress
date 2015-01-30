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

/**
 * The InvariantChecks class provides static methods for checking different kinds
 * of invariants. If a check fails a corresponding exception is thrown.
 * 
 * @author Andrei Tatarnikov
 */

public final class InvariantChecks {
  private InvariantChecks() {}

  /**
   * Checks the invariant "Object reference is not null" and
   * throws an exception if it is violated. 
   * 
   * @param o Object reference to be checked.
   * 
   * @throws NullPointerException if the invariant is violated ({@code o} is {@code null}).
   */

  public static void checkNotNull(Object o) {
    if (null == o) {
      throw new NullPointerException();
    }
  }

  /**
   * Checks the invariant "Object reference is not {@code null}" and
   * throws an exception if it is violated. 
   * 
   * @param o Object reference to be checked.
   * @param name Name of the variable that stores the object reference. 
   * 
   * @throws NullPointerException if the invariant is violated ({@code o} is {@code null}).
   */

  public static void checkNotNull(Object o, String name) {
    if (null == o) {
      throw new NullPointerException(
          String.format("%s must not be equal null", name));
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

  public static void checkGreaterThanZero(int n) {
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

  public static void checkGreaterOrEqZero(int n) {
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

  public static void checkBounds(int index, int length) {
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

  public static void checkBoundsInclusive(int index, int length) {
    if (!(0 <= index && index <= length)) {
      throw new IndexOutOfBoundsException(String.format(
          "%d must be within range [0, %d]", index, length));
    }
  }
}
