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

package ru.ispras.fortress.expression.printer;

import ru.ispras.fortress.expression.ExprTreeVisitorDefault;
import ru.ispras.fortress.expression.ExprTreeWalker;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.util.InvariantChecks;

import java.util.EnumMap;

/**
 * This class implements an abstract map-based expression printer.
 * 
 * @author <a href="mailto:kamkin@ispras.ru">Alexander Kamkin</a>
 */
public abstract class MapBasedPrinter implements ExprTreePrinter {
  /**
   * This class implements an expression tree visitor that prints an expression by using a map of
   * operation identifiers to operation descriptions.
   */
  protected class ExprTreeVisitor extends ExprTreeVisitorDefault {
    /** Keeps the intermediate expression text. */
    private StringBuffer buffer;

    /** Specifies the order of operands traversal. */
    private int[] operandOrder;

    /**
     * Sets up the initial state of the walker before starting visiting
     * an expression tree.
     */
    private final void init() {
      buffer = new StringBuffer();
    }

    /**
     * Appends text to the string representation of the expression tree.
     * 
     * @param text Text to be appended.
     */
    protected final void appendText(final String text) {
      InvariantChecks.checkNotNull(buffer, "Visitor is not initialized");
      buffer.append(text);
    }

    /**
     * Returns the string representation of the expression tree.
     * 
     * @return the string representation of the expression tree.
     */
    public final String toString() {
      return buffer.toString();
    }

    @Override
    public void onOperationBegin(final NodeOperation expr) {
      final OperationDescription description = getOperationDescription(expr);

      if (description == null) {
        throw new IllegalArgumentException(
            String.format("Unknown operation '%s'", expr.getOperationId()));
      }

      final String prefix = description.getPrefix();

      if (prefix != null) {
        appendText(prefix);
      }

      operandOrder = description.getOrder();
    }

    @Override
    public int[] getOperandOrder() {
      return operandOrder;
    }

    @Override
    public void onOperationEnd(final NodeOperation expr) {
      final OperationDescription description = getOperationDescription(expr);
      final String suffix = description.getSuffix();

      if (suffix != null) {
        appendText(suffix);
      }
    }

    @Override
    public void onOperandBegin(
        final NodeOperation expr,
        final Node operand,
        final int index) {
      final OperationDescription description = getOperationDescription(expr);

      if (index > 0) {
        final String infix = description.getInfix(index - 1);

        if (infix != null) {
          appendText(infix);
        }
      }
    }

    @Override
    public void onValue(final NodeValue value) {
      appendText(value.toString());
    }

    @Override
    public void onVariable(final NodeVariable variable) {
      appendText(variable.getName());
    }
  }

  /** Maps the operation identifiers to the operation descriptions. */
  private final EnumMap<StandardOperation, OperationDescription> map;

  /** Creates textual representation of specific nodes by visiting them. */
  private ExprTreeVisitor visitor;

  /**
   * Constructs a map-based expression printer.
   */
  protected MapBasedPrinter() {
    this.map = new EnumMap<>(StandardOperation.class);
    this.visitor = new ExprTreeVisitor();
  }

  /**
   * Returns operation description for the specified operation expression.
   * 
   * @param expr Operation expression.
   * @return {@link OperationDescription} object or {@code null} if the operation
   *         is not registered.
   */
  protected OperationDescription getOperationDescription(final NodeOperation expr) {
    return map.get(expr.getOperationId());
  }

  /**
   * Customizes printer behavior by setting a customized visitor. 
   * 
   * @param visitor Custom visitor implementation.
   */
  protected void setVisitor(final ExprTreeVisitor visitor) {
    InvariantChecks.checkNotNull(visitor);
    this.visitor = visitor;
  }

  /**
   * Adds a mapping between the operation identifier and the operation description.
   * 
   * @param op the operation identifier.
   * @param prefix the operation prefix.
   * @param infix the operation infixes.
   * @param suffix the operation suffix.
   */
  protected final void addMapping(
      final StandardOperation op,
      final String prefix,
      final String[] infix,
      final String suffix) {
    map.put(op, new OperationDescription(prefix, infix, suffix));
  }

  /**
   * Adds a mapping between the operation identifier and the operation description.
   * 
   * @param op the operation identifier.
   * @param prefix the operation prefix.
   * @param infix the operation infixes.
   * @param suffix the operation suffix.
   * @param order the order of operands.
   */
  protected final void addMapping(
      final StandardOperation op,
      final String prefix,
      final String[] infix,
      final String suffix,
      final int[] order) {
    map.put(op, new OperationDescription(prefix, infix, suffix, order));
  }

  /**
   * Adds a mapping between the operation identifier and the operation description.
   * 
   * @param op the operation identifier.
   * @param prefix the operation prefix.
   * @param infix the operation infix.
   * @param suffix the operation suffix.
   */
  protected final void addMapping(
      final StandardOperation op,
      final String prefix,
      final String infix,
      final String suffix) {
    map.put(op, new OperationDescription(prefix, infix, suffix));
  }

  /**
   * Adds a mapping between the operation identifier and the operation description.
   * 
   * @param op the operation identifier.
   * @param sign the operation sign.
   * @param type the operation type.
   * @param addSpaces the flag indicating whether spaces before and after the operation sign are
   *        required.
   */
  protected final void addMapping(
      final StandardOperation op,
      final String sign,
      final OperationDescription.Type type,
      final boolean addSpaces) {
    map.put(op, new OperationDescription(sign, type, addSpaces));
  }

  /**
   * Adds a mapping between the operation identifier and the operation description.
   * 
   * @param op the operation identifier.
   * @param sign the operation sign.
   * @param type the operation type.
   */
  protected final void addMapping(
      final StandardOperation op,
      final String sign,
      final OperationDescription.Type type) {
    map.put(op, new OperationDescription(sign, type));
  }

  /**
   * Adds a mapping between the operation identifier and the operation description.
   * 
   * @param op the operation identifier.
   * @param sign the operation signs.
   * @param addSpaces the flag indicating whether spaces before and after the operation sign are
   *        required.
   * @param order the order of operands.
   */
  protected final void addMapping(
      final StandardOperation op,
      final String[] sign,
      final boolean addSpaces,
      final int[] order) {
    map.put(op, new OperationDescription(sign, addSpaces, order));
  }

  /**
   * Adds a mapping between the operation identifier and the operation description.
   * 
   * @param op the operation identifier.
   * @param sign the operation signs.
   * @param addSpaces the flag indicating whether spaces before and after the operation sign are
   *        required.
   */
  protected final void addMapping(
      final StandardOperation op,
      final String[] sign,
      final boolean addSpaces) {
    map.put(op, new OperationDescription(sign, addSpaces));
  }

  /**
   * Adds a mapping between the operation identifier and the operation description.
   * 
   * @param op the operation identifier.
   * @param sign the operation signs.
   * @param order the order of operands.
   */
  protected final void addMapping(final StandardOperation op, final String[] sign,
      final int[] order) {
    map.put(op, new OperationDescription(sign, order));
  }

  /**
   * Adds a mapping between the operation identifier and the operation description.
   * 
   * @param op the operation identifier.
   * @param sign the operation signs.
   */
  protected final void addMapping(final StandardOperation op, final String[] sign) {
    map.put(op, new OperationDescription(sign));
  }

  @Override
  public final String toString(final Node node) {
    final ExprTreeWalker walker = new ExprTreeWalker(visitor);
    visitor.init();

    walker.visit(node);
    return visitor.toString();
  }
}
