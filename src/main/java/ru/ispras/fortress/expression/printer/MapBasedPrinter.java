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

package ru.ispras.fortress.expression.printer;

import java.util.EnumMap;

import ru.ispras.fortress.expression.ExprTreeVisitorDefault;
import ru.ispras.fortress.expression.ExprTreeWalker;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.StandardOperation;

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

  final class ExprTreeVisitor extends ExprTreeVisitorDefault {
    /** Maps the operation identifiers to the operation descriptions. */
    private EnumMap<StandardOperation, OperationDescription> map;

    /** Keeps the intermediate expression text. */
    private StringBuffer buffer = new StringBuffer();

    /**
     * Constructs an expression tree visitor.
     * 
     * @param map the map of operations to operation descriptions.
     */

    public ExprTreeVisitor(final EnumMap<StandardOperation, OperationDescription> map) {
      if (map == null) {
        throw new NullPointerException();
      }

      this.map = map;
    }

    /**
     * Returns the string representation of the expression tree.
     * 
     * @return the string representation of the expression tree.
     */

    public String toString() {
      return buffer.toString();
    }

    @Override
    public void onOperationBegin(final NodeOperation expr) {
      final Enum<?> op = expr.getOperationId();
      final OperationDescription description = map.get(op);

      if (description == null) {
        throw new IllegalArgumentException(String.format("Unknown operation '%s'", op.name()));
      }

      final String prefix = description.getPrefix();

      if (prefix != null) {
        buffer.append(prefix);
      }
    }

    @Override
    public void onOperationEnd(final NodeOperation expr) {
      final OperationDescription description = map.get(expr.getOperationId());
      final String suffix = description.getSuffix();

      if (suffix != null) {
        buffer.append(suffix);
      }
    }

    @Override
    public void onOperandBegin(final NodeOperation expr, final Node operand, int index) {
      final OperationDescription description = map.get(expr.getOperationId());

      if (index > 0) {
        final String infix = description.getInfix(index - 1);

        if (infix != null) {
          buffer.append(infix);
        }
      }
    }

    @Override
    public void onValue(final NodeValue value) {
      buffer.append(value.toString());
    }

    @Override
    public void onVariable(final NodeVariable variable) {
      buffer.append(variable.getName());
    }
  }

  /** Maps the operation identifiers to the operation descriptions. */

  private EnumMap<StandardOperation, OperationDescription> map =
      new EnumMap<StandardOperation, OperationDescription>(StandardOperation.class);

  /**
   * Constructs a map-based expression printer.
   */

  protected MapBasedPrinter() {}

  /**
   * Adds a mapping between the operation identifier and the operation description.
   * 
   * @param op the operation identifier.
   * @param prefix the operation prefix.
   * @param infix the operation infixes.
   * @param suffix the operation suffix.
   */

  protected final void addMapping(final StandardOperation op, final String prefix,
      final String[] infix, final String suffix) {
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

  protected final void addMapping(final StandardOperation op, final String prefix,
      final String[] infix, final String suffix, final int[] order) {
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

  protected final void addMapping(final StandardOperation op, final String prefix,
      final String infix, final String suffix) {
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

  protected final void addMapping(final StandardOperation op, final String sign,
      final OperationDescription.Type type, boolean addSpaces) {
    map.put(op, new OperationDescription(sign, type, addSpaces));
  }

  /**
   * Adds a mapping between the operation identifier and the operation description.
   * 
   * @param op the operation identifier.
   * @param sign the operation sign.
   * @param type the operation type.
   */

  protected final void addMapping(final StandardOperation op, final String sign,
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

  protected final void addMapping(final StandardOperation op, final String[] sign,
      boolean addSpaces, final int[] order) {
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

  protected final void addMapping(final StandardOperation op, final String[] sign,
      boolean addSpaces) {
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
    final ExprTreeVisitor visitor = new ExprTreeVisitor(map);
    final ExprTreeWalker walker = new ExprTreeWalker(visitor);

    walker.visit(node);
    return visitor.toString();
  }
}
