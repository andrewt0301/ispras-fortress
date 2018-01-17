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

package ru.ispras.fortress.expression;

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.util.InvariantChecks;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

/**
 * The {@link NodeBinding} class represents set of substitutions to be considered in underlying
 * expression subtree. List of bound variables considered immutable.
 */
public final class NodeBinding extends Node {
  /**
   * The {@link BoundVariable} class represents key-value binding pair.
   */
  public static final class BoundVariable {
    private final NodeVariable variable;
    private final Node value;

    private BoundVariable(final NodeVariable variable, final Node value) {
      this.variable = variable;
      this.value = value;
    }

    /**
     * Returns object representing bound variable.
     * 
     * @return A bound variable object reference.
     */
    public NodeVariable getVariable() {
      return variable;
    }

    /**
     * Returns bound value object.
     * 
     * @return A bound value.
     */
    public Node getValue() {
      return value;
    }

    @Override
    public int hashCode() {
      final int prime = 31;
      return prime * variable.hashCode() + value.hashCode();
    }

    @Override
    public boolean equals(final Object rhs) {
      if (rhs == null) {
        return false;
      }

      if (rhs == this) {
        return true;
      }

      if (this.getClass() != rhs.getClass()) {
        return false;
      }

      final BoundVariable binding = (BoundVariable) rhs;
      return variable.equals(binding.variable) && value.equals(binding.value);
    }
  }

  private Node expr;
  private List<BoundVariable> bindings;

  /**
   * Creates a node based on expression and list of bindings. List of bound variables considered
   * immutable therefore incurring need for copying input list. List is sorted because equality
   * comparison relies on order of bindings.
   * 
   * @param expression Expression subtree.
   * @param bindings List of bound variables.
   */
  public NodeBinding(
      final Node expression,
      final List<BoundVariable> bindings) {
    super(Kind.BINDING);

    InvariantChecks.checkNotNull(expression);
    InvariantChecks.checkNotNull(bindings);

    this.expr = expression;

    if (bindings.isEmpty()) {
      this.bindings = Collections.emptyList();
    } else {
      this.bindings = new ArrayList<>(bindings);
    }

    final Comparator<BoundVariable> cmp = new Comparator<BoundVariable>() {
      public int compare(final BoundVariable lhs, final BoundVariable rhs) {
        InvariantChecks.checkNotNull(lhs);
        InvariantChecks.checkNotNull(rhs);
        return lhs.getVariable().getName().compareTo(rhs.getVariable().getName());
      }
    };

    Collections.sort(this.bindings, cmp);
  }

  /**
   * Constructs a node based on an expression and a variable number of bindings.
   * See constructor {@code NodeBinding(Node expression, List<BoundVariable> bindings)}.
   *
   * @param expression Expression subtree.
   * @param bindings Bound variables.
   */
  public NodeBinding(final Node expression, final BoundVariable... bindings) {
    this(expression, Arrays.asList(bindings));
  }

  /**
   * Constructor to avoid redundant allocations. Do not incur sorting.
   *
   * @param expr Expression subtree.
   * @param bindings List of bound variables.
   */
  private NodeBinding(
      final Node expr,
      final List<BoundVariable> bindings,
      final int unused) {
    super(Kind.BINDING);

    this.expr = expr;
    this.bindings = bindings;
  }

  /**
   * Returns list of bound variables associated with the node.
   *
   * @return Unmodifiable list of bound variables.
   */
  public List<BoundVariable> getBindings() {
    return Collections.unmodifiableList(bindings);
  }

  /**
   * Returns underlying expression subtree.
   *
   * @return An expression.
   */
  public Node getExpression() {
    return expr;
  }

  public Node deepCopy() {
    return new NodeBinding(this.expr, this.bindings, 0);
  }

  /**
   * Create binding node with same bindings for given expression. Avoids additional costs of using
   * constructor directly.
   *
   * @param expression An expression subtree.
   *
   * @return A binding node object.
   */
  public NodeBinding bindTo(final Node expression) {
    return new NodeBinding(expression, this.bindings, 0);
  }

  /**
   * Create bound variable using NodeVariable object and expression.
   *
   * @param variable An object representing bound variable.
   * @param value A bound value.
   *
   * @return A bound variable object.
   */
  public static BoundVariable bindVariable(
      final NodeVariable variable,
      final Node value) {
    InvariantChecks.checkNotNull(variable);
    InvariantChecks.checkNotNull(value);
    return new BoundVariable(variable, value);
  }

  @Override
  public DataType getDataType() {
    return expr.getDataType();
  }

  @Override
  public String toString() {
    final StringBuilder builder = new StringBuilder();

    builder.append("(LET (");
    for (final BoundVariable bound : getBindings()) {
      builder.append('(');
      builder.append(bound.getVariable().toString());
      builder.append(' ');
      builder.append(bound.getValue().toString());
      builder.append(')');
    }

    builder.append(") ");
    builder.append(getExpression().toString());
    builder.append(')');

    return builder.toString();
  }

  @Override
  public int hashCode() {
    final int prime = 31;
    return expr.hashCode() * prime + bindings.hashCode();
  }

  @Override
  public boolean equals(final Object rhs) {
    if (rhs == null) {
      return false;
    }

    if (rhs == this) {
      return true;
    }

    if (this.getClass() != rhs.getClass()) {
      return false;
    }

    final NodeBinding node = (NodeBinding) rhs;
    return this.bindings.equals(node.bindings);
  }
}
