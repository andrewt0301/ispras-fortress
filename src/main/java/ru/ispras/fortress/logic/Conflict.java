/*
 * Copyright 2014 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.logic;

/**
 * This class represents a conflict of two literals.
 * 
 * @author <a href="mailto:kamkin@ispras.ru">Alexander Kamkin</a>
 */
public final class Conflict {
  /** The left-hand-side variable (i.e., a variable with a lower identifier) of the conflict. */
  private final int lhs;
  /** The right-hand-side variable (i.e., a variable with a higher identifier) of the conflict. */
  private final int rhs;
  /** The flag indicating whether the conflicting variables have different signs. */
  private final boolean differentSigns;

  /**
   * Constructs a conflict.
   * 
   * @param lhs variable 1.
   * @param rhs variable 2.
   * @param differentSigns the different-signs flag.
   */
  public Conflict(final int lhs, final int rhs, final boolean differentSigns) {
    if (lhs == rhs) {
      throw new IllegalArgumentException("A variable cannot conflict with itself");
    }

    this.lhs = lhs < rhs ? lhs : rhs;
    this.rhs = lhs < rhs ? rhs : lhs;

    this.differentSigns = differentSigns;
  }

  /**
   * Constructs a conflict.
   * 
   * @param lhs variable 1.
   * @param rhs variable 2.
   */
  public Conflict(final int lhs, final int rhs) {
    this(lhs, rhs, false);
  }

  /**
   * The left-hand-side variable (i.e., a variable with a lower identifier) of the conflict.
   * 
   * @return the left-hand-side variable.
   */
  public int getLhsVar() {
    return lhs;
  }

  /**
   * The right-hand-side variable (i.e., a variable with a higher identifier) of the conflict.
   * 
   * @return the right-hand-side variable.
   */
  public int getRhsVar() {
    return rhs;
  }

  /**
   * Check whether the conflicting variables have different signs.
   * 
   * @return <code>true</code> if the conflicting variables have different signs; <code>false</code>
   *         otherwise.
   */
  public boolean areDifferentSigns() {
    return differentSigns;
  }

  @Override
  public int hashCode() {
    return ((differentSigns ? 1 : 0) << 31) ^ (lhs << 16) ^ rhs;
  }

  @Override
  public boolean equals(final Object o) {
    if (!(o instanceof Conflict)) {
      return false;
    }

    final Conflict r = (Conflict) o;
    return lhs == r.lhs && rhs == r.rhs && differentSigns == r.differentSigns;
  }
}
