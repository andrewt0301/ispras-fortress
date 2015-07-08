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

package ru.ispras.fortress.expression.printer;

/**
 * This class contains information on operation mapping.
 * 
 * @author <a href="mailto:kamkin@ispras.ru">Alexander Kamkin</a>
 */

public final class OperationDescription {
  /**
   * This enumeration contains the operation types.
   */

  public enum Type {
    /** The prefix operation. */
    PREFIX,
    /** The infix operation. */
    INFIX,
    /** The suffix operation. */
    SUFFIX
  }

  /** The operation prefix (string written before the first operand). */
  private String prefix;

  /** The operation infix(es) (string(s) written between two operands). */
  private String[] infix;

  /** The operation suffix (string written after the last operand). */
  private String suffix;

  /** The order of operands. */
  private int[] order;

  /**
   * Constructs an operation description.
   * 
   * @param prefix the operation prefix.
   * @param infix the operation infixes.
   * @param suffix the operation suffix.
   * @param order the order of operands.
   */

  public OperationDescription(
      final String prefix,
      final String[] infix,
      final String suffix,
      final int[] order) {
    this.prefix = prefix;
    this.infix = infix;
    this.suffix = suffix;
    this.order = order;
  }

  /**
   * Constructs an operation description.
   * 
   * @param prefix the operation prefix.
   * @param infix the operation infixes.
   * @param suffix the operation suffix.
   */

  public OperationDescription(
      final String prefix,
      final String[] infix,
      final String suffix) {
    this(prefix, infix, suffix, null);
  }

  /**
   * Constructs an operation description.
   * 
   * @param prefix the operation prefix.
   * @param infix the operation infix.
   * @param suffix the operation suffix.
   */

  public OperationDescription(
      final String prefix,
      final String infix,
      final String suffix) {
    this(prefix, new String[] {infix}, suffix);
  }

  /**
   * Constructs an operation description.
   * 
   * @param sign the operation sign.
   * @param type the operation type.
   * @param addSpaces the flag indicating whether spaces before and after the operation sign are
   *        required.
   */

  public OperationDescription(
      final String sign,
      final Type type,
      final boolean addSpaces) {
    final String modifiedSign = addSpaces ? String.format(" %s ", sign) : sign;

    switch (type) {
      case PREFIX:
        prefix = modifiedSign;
        break;

      case INFIX:
        prefix = "(";
        infix = new String[] {modifiedSign};
        suffix = ")";
        break;

      case SUFFIX:
        suffix = sign;
        break;
    }
  }

  /**
   * Constructs an operation description.
   * 
   * @param sign the operation sign.
   * @param type the operation type.
   */

  public OperationDescription(final String sign, final Type type) {
    this(sign, type, true);
  }

  /**
   * Constructs an operation description.
   * 
   * @param sign the operation signs.
   * @param addSpaces the flag indicating whether spaces before and after the operation sign are
   *        required.
   * @param order the order of operands.
   */

  public OperationDescription(
      final String[] sign,
      final boolean addSpaces,
      final int[] order) {
    final String[] modifiedSign = new String[sign.length];

    for (int i = 0; i < sign.length; i++) {
      modifiedSign[i] = addSpaces ? String.format(" %s ", sign[i]) : sign[i];
    }

    prefix = "(";
    infix = modifiedSign;
    suffix = ")";

    this.order = order;
  }
  
  /**
   * Constructs an operation description.
   * 
   * @param sign the operation signs.
   * @param addSpaces the flag indicating whether spaces before and after the operation sign are
   *        required.
   */

  public OperationDescription(
      final String[] sign,
      final boolean addSpaces) {
    this(sign, addSpaces, null);
  }

  /**
   * Constructs an operation description.
   * 
   * @param sign the operation signs.
   * @param order the order of operands.
   */

  public OperationDescription(
      final String[] sign,
      final int[] order) {
    this(sign, true, order);
  }

  /**
   * Constructs an operation description.
   * 
   * @param sign the operation signs.
   */

  public OperationDescription(final String[] sign) {
    this(sign, null);
  }

  /**
   * Returns the operation prefix (string written before the first operand).
   * 
   * @return the operation prefix.
   */

  public String getPrefix() {
    return prefix;
  }

  /**
   * Returns the operation infix (string written between two operands).
   * 
   * @return the operation infix.
   */

  public String getInfix() {
    return infix[0];
  }

  /**
   * Returns the <code>i</code>-th operation infix (string written between <code>i</code>-th and
   * <code>(i+1)</code>-th operands).
   * 
   * @return the <code>i</code>-th operation infix.
   */

  public String getInfix(final int i) {
    return infix.length == 1 ? infix[0] : infix[i];
  }

  /**
   * Returns the operation suffix (string written after the last operand).
   * 
   * @return the operation suffix.
   */

  public String getSuffix() {
    return suffix;
  }

  /**
   * Returns the order of operands.
   * 
   * @return the array specifying the order of operands or <code>null</code> for the standard order.
   */

  public int[] getOrder() {
    return order;
  }
}
