/*
 * Copyright 2011-2018 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.solver.constraint;

import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.ExprUtils;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.Nodes;
import ru.ispras.fortress.util.InvariantChecks;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

/**
 * The {@link Formulas} class serves as a container for formula expressions (assertions) that
 * specify the invariants for a taken constraint.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public final class Formulas {
  private final List<Node> exprs;

  /**
   * Constructs an empty formula container.
   */
  public Formulas() {
    this.exprs = new ArrayList<>();
  }

  /**
   * Constructs a new formula container by copying the contents of an existing one.
   *
   * @param formulas Existing formula container.
   *
   * @throws IllegalArgumentException if the parameter equals {@code null}.
   */
  public Formulas(final Formulas formulas) {
    InvariantChecks.checkNotNull(formulas);
    this.exprs = new ArrayList<>(formulas.exprs);
  }

  /**
   * Constructs a container than contains the specified formula.
   *
   * @param formula A formula to be placed in the container.
   */
  public Formulas(final Node formula) {
    this();
    add(formula);
  }

  /**
   * Adds a formula expression to the formula container.
   *
   * @param formula A formula expression.
   *
   * @throws IllegalArgumentException if the parameter equals {@code null}.
   */
  public void add(final Node formula) {
    InvariantChecks.checkNotNull(formula);
    exprs.add(formula);
  }

  /**
   * Adds all formula expression from the specified collection to the formula container.
   *
   * @param formulas A collection of formula expressions.
   *
   * @throws IllegalArgumentException if the parameter equals {@code null}.
   */
  public void addAll(final Collection<? extends Node> formulas) {
    InvariantChecks.checkNotNull(formulas);
    for (final Node formula : formulas) {
      add(formula);
    }
  }

  /**
   * Adds all formula expressions from the specified formula container to
   * the current formula container.
   *
   * @param formulas Formula container to be copied.
   *
   * @throws IllegalArgumentException if the parameter equals {@code null}.
   */
  public void addAll(final Formulas formulas) {
    InvariantChecks.checkNotNull(formulas);
    addAll(formulas.exprs);
  }

  /**
   * Provides access to the list of formula expressions.
   *
   * @return List of formula expressions
   */
  public List<Node> exprs() {
    return Collections.unmodifiableList(exprs);
  }

  /**
   * Unites all stored formula expressions into a single expression using
   * the AND operator and returns it to the client.
   *
   * @return A single expression for all stored formula expressions.
   */
  public Node asSingleExpr() {
    Node root = null;

    for (final Node item : exprs()) {
      root = (null == root) ? item : Nodes.and(root, item);
    }

    return root;
  }

  /**
   * Finds all variables used in the stored formula expressions and returns them to the client.
   *
   * @return A list of all variables used in the stored formula expressions.
   *
   * @throws IllegalStateException if the method finds nodes that refer to different variable
   *         instances that have the same name. This is illegal because all variables used in
   *         formula expression of a constraint must be accessible via its variable table (the
   *         signature of the constraint).
   */
  public List<Variable> getVariables() {
    final Collection<NodeVariable> nodeVariables = ExprUtils.getVariables(exprs());
    final List<Variable> variables = new ArrayList<>(nodeVariables.size());

    for (final NodeVariable nodeVariable : nodeVariables) {
      variables.add(nodeVariable.getVariable());
    }

    return Collections.unmodifiableList(variables);
  }

  @Override
  public int hashCode() {
    return exprs.hashCode();
  }

  @Override
  public boolean equals(final Object obj) {
    if (this == obj) {
      return true;
    }

    if (obj == null) {
      return false;
    }

    if (getClass() != obj.getClass()) {
      return false;
    }

    final Formulas other = (Formulas) obj;
    if (!exprs.equals(other.exprs)) {
      return false;
    }

    return true;
  }

  @Override
  public String toString() {
    return exprs.toString();
  }
}
