/*
 * Copyright 2013-2014 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.calculator;

import static ru.ispras.fortress.util.InvariantChecks.checkGreaterThanZero;

/**
 * The ArityRange class is used to specify a possible arity of an operator (unary, binary, etc.). It
 * is possible for an operator to be unary and binary at the same time or to have an unlimited
 * number of operands. The Range class allows specifying a range for the allowed number of operands.
 * 
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public final class ArityRange {
  /**
   * The Bound enumeration contains constants for specifying most common bounds for the range of
   * allowed operand numbers.
   * 
   * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
   */
  public static enum Bound {
    /** Bound for unary operators. */
    UNARY(1),

    /** Bound for binary operators. */
    BINARY(2),

    /** Bound for ternary operators. */
    TERNARY(3),

    /** Bound for unlimited number of operands. */
    UNBOUNDED(-1);

    private final int value;

    private Bound(final int value) {
      this.value = value;
    }

    /**
     * Returns the number that corresponds to the given bound constant.
     * 
     * @return Numeric value for the bound.
     */
    public int value() {
      return value;
    }
  }

  /** Unary operator range. */
  public static final ArityRange UNARY = new ArityRange(Bound.UNARY, Bound.UNARY);

  /** Binary operator range. */
  public static final ArityRange BINARY = new ArityRange(Bound.BINARY, Bound.BINARY);

  /** Ternary operator range. */
  public static final ArityRange TERNARY = new ArityRange(Bound.TERNARY, Bound.TERNARY);

  /** Range for operators that can be unary and binary at the same time. */
  public static final ArityRange UNARY_BINARY = new ArityRange(Bound.UNARY, Bound.BINARY);

  /** Range for operators that can have one (unary) or an unbounded number of operands. */
  public static final ArityRange UNARY_UNBOUNDED = new ArityRange(Bound.UNARY, Bound.UNBOUNDED);

  /** Range for operators that can have two (binary) or an unbounded number of operands. */
  public static final ArityRange BINARY_UNBOUNDED = new ArityRange(Bound.BINARY, Bound.UNBOUNDED);

  private final int min;
  private final int max;

  /**
   * Creates a range basing on the specified bounds.
   * 
   * @param min Lower bound.
   * @param max Upper bound.
   */
  public ArityRange(final Bound min, final Bound max) {
    this(min.value(), max.value());
  }

  /**
   * Creates a range basing on the specified boundary values.
   * 
   * @param min Lower boundary value.
   * @param max Upper boundary value.
   * 
   * @throws IllegalArgumentException if the range is specified incorrectly.
   */
  public ArityRange(final int min, final int max) {
    checkGreaterThanZero(min);

    if (!((min <= max) || (max == Bound.UNBOUNDED.value()))) {
      throw new IllegalArgumentException();
    }

    this.min = min;
    this.max = max;
  }

  /**
   * Checks whether the specified value falls within the range of allowed values.
   * 
   * @param value Number of operands.
   * @return {@code true} if value is in the range or {@code false} otherwise.
   */
  public boolean isWithinRange(final int value) {
    return (min <= value) && ((value <= max) || (Bound.UNBOUNDED.value() == max));
  }
}
