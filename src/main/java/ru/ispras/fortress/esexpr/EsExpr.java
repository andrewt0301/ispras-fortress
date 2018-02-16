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

package ru.ispras.fortress.esexpr;

import ru.ispras.fortress.util.InvariantChecks;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

/**
 * The {@link EsExpr} class represents Lisp-like S-expressions using tuple notation.
 * EsExpr can be atom, i.e. string literal, or expression of form (a . b . c ...)
 * which is equivalent for traditional dotted-pair sequence (a . (b . (c . ...))).
 * This kind of expressions is called tuples. Tuples with special atom NIL
 * at the last position are called lists. NIL is a predefined atom which
 * is considered as an empty tuple or list.
 */
public final class EsExpr {
  public static final EsExpr NIL =
      new EsExpr("NIL", Collections.<EsExpr>emptyList());

  private static final String LIST_LITERAL = "<list>";
  private static final String TUPLE_LITERAL = "<tuple>";

  private final String literal;
  private final List<EsExpr> items;

  private EsExpr(final String literal, final List<EsExpr> items) {
    this.literal = literal;
    this.items = items;
  }

  /**
   * Returns {@code true} if this expression is atom.
   *
   * @return {@code true} if this expression is atom
   */
  public boolean isAtom() {
    return items.isEmpty();
  }

  /**
   * Returns {@code true} if this expression is {@code NIL} atom.
   *
   * @return {@code true} if this expression is {@code NIL} atom
   */
  public boolean isNil() {
    return this == NIL;
  }

  /**
   * Returns {@code true} if this expression is list.
   * List expression is {@code NIL} atom or tuple containing {@code NIL}
   * at last position.
   *
   * @return {@code true} if this expression is list
   */
  public boolean isList() {
    return this.isNil() || !this.isAtom() && items.get(items.size() - 1).isNil();
  }

  /**
   * Returns {@code true} if this expression is tuple.
   *
   * @return {@code true} if this expression is tuple
   */
  public boolean isTuple() {
    return this.isNil() || !this.isAtom();
  }

  /**
   * Returns string literal for given expression.
   * Atom string literal evaluates to itself, list and tuple literals are
   * predefined strings denoting how expression has been created. If correct
   * string representation required for S-expression, use {@link #toString() }
   * instead.
   *
   * @return string literal for this expression
   */
  public String getLiteral() {
    return literal;
  }

  /**
   * Returns list of S-expressions contained in this expression.
   *
   * @return list of contained expressions, empty list for atoms
   */
  public List<EsExpr> getItems() {
    return Collections.unmodifiableList(items);
  }

  /**
   * Returns list of S-expressions contained in this list excluding last {@code NIL}.
   *
   * @return list of contained expressions excluding last {@code NIL}
   * @throws UnsupportedOperationException if this expression is not list
   */
  public List<EsExpr> getListItems() {
    if (!this.isList()) {
      throw new UnsupportedOperationException("getListItems is defined only for S-lists");
    }
    if (this.isNil()) {
      return items;
    }
    return Collections.unmodifiableList(items.subList(0, items.size() - 1));
  }

  @Override
  public boolean equals(final Object obj) {
    if (obj == null) {
      return false;
    }
    if (obj == this) {
      return true;
    }
    if (this.getClass() != obj.getClass()) {
      return false;
    }
    final EsExpr e = (EsExpr) obj;
    if (e.isNil() || this.isNil()
        || e.isAtom() != this.isAtom()
        || e.isList() != this.isList()) {
      return false;
    }
    if (e.isAtom()) {
      return getLiteral().equals(e.getLiteral());
    }
    if (e.items.size() != this.items.size()) {
      return false;
    }
    for (int i = 0; i < items.size(); ++i) {
      if (!items.get(i).equals(e.items.get(i))) {
        return false;
      }
    }
    return true;
  }

  @Override
  public String toString() {
    if (this.isAtom()) {
      return this.getLiteral();
    }
    final StringBuilder builder = new StringBuilder();
    this.toString(builder);
    return builder.toString();
  }

  /**
   * Helper method for writing string representation of this expression
   * into StringBuilder.
   *
   * @param builder StringBuilder to write into.
   */
  private void toString(final StringBuilder builder) {
    if (this.isAtom()) {
      builder.append(this.getLiteral());
      return;
    }
    builder.append('(');
    if (this.isList()) {
      printList(builder);
    } else {
      printTuple(builder);
    }
    builder.append(')');
  }

  /**
   * Helper method for writing string representation of this list
   * into StringBuilder. List syntax-sugar is being used, i.e.
   * (a . b . c . NIL) being written as (a b c).
   *
   * @param builder StringBuilder to write into.
   */
  private void printList(final StringBuilder builder) {
    final String delim = " ";
    for (int i = 0; i < items.size() - 1; ++i) {
      items.get(i).toString(builder);
      builder.append(delim);
    }
    builder.delete(builder.length() - delim.length(), builder.length());
  }

  /**
   * Helper method for writing string representation of this tuple
   * into StringBuilder. Dotted-tuple notation is used, i.e. strings
   * like (a . b . c).
   *
   * @param builder StringBuilder to write into.
   */
  private void printTuple(final StringBuilder builder) {
    final String delim = " . ";
    for (final EsExpr e : items) {
      e.toString(builder);
      builder.append(delim);
    }
    builder.delete(builder.length() - delim.length(), builder.length());
  }

  /**
   * Returns shallowest equivalent of this expression. I.e. transforms
   * recursively tuples like (a . b . (c . d)) into (a . b . c . d) form.
   *
   * @return shallowest equivalent of this expression.
   */
  public EsExpr normalizeTuples() {
    if (this.isAtom()) {
      return this;
    }
    final ArrayList<EsExpr> normItems = new ArrayList<>(items.size());
    boolean update = false;
    for (final EsExpr e : items) {
      final EsExpr norm = e.normalizeTuples();
      normItems.add(norm);
      update = update || norm != e;
    }
    final EsExpr last = normItems.get(normItems.size() - 1);
    if (this.isTuple() && last.isTuple() && !last.isNil()) {
      normItems.remove(normItems.size() - 1);
      normItems.addAll(last.getItems());
      update = true;
    }
    if (!update) {
      return this;
    }
    normItems.trimToSize();
    return new EsExpr(TUPLE_LITERAL, normItems);
  }

  /**
   * Returns deepest equivalent of this expression. I.e. returns
   * expression consisting only of dotted pairs and atoms.
   *
   * @return deepest equivalent of this expression.
   */
  public EsExpr normalizePairs() {
    if (this.isAtom()) {
      return this;
    }
    if (this.items.size() == 2) {
      final EsExpr lhs = items.get(0).normalizePairs();
      final EsExpr rhs = items.get(1).normalizePairs();
      if (lhs == items.get(0) && rhs == items.get(1)) {
        return this;
      }
      return cons(lhs, rhs);
    }
    EsExpr last = items.get(items.size() - 1).normalizePairs();
    for (int i = items.size() - 2; i >= 0; --i) {
      last = cons(items.get(i).normalizePairs(), last);
    }
    return last;
  }

  /**
   * Create atom for given string literal.
   *
   * @param literal string literal for atom being created
   * @return atom for given string literal
   * @throws IllegalArgumentException if {@code literal} is {@code null}
   */
  public static EsExpr createAtom(final String literal) {
    InvariantChecks.checkNotNull(literal);
    if (literal.equalsIgnoreCase(NIL.getLiteral())) {
      return NIL;
    }
    return new EsExpr(literal, Collections.<EsExpr>emptyList());
  }

  /**
   * Create list of given S-expressions. Adds {@code NIL} atom at the end
   * of list.
   *
   * @param items list of S-expressions
   * @return list containing all expressions from {@code items} list
   * @throws IllegalArgumentException if {@code items} list is {@code null}
   */
  public static EsExpr createList(final List<EsExpr> items) {
    InvariantChecks.checkNotNull(items);
    if (items.isEmpty()) {
      return NIL;
    }
    final ArrayList<EsExpr> list = new ArrayList<>(items.size() + 1);
    list.addAll(items);
    list.add(NIL);
    return new EsExpr(LIST_LITERAL, list);
  }

  /**
   * Create tuple of given S-expressions.
   *
   * @param items list of S-expressions
   * @return tuple containing all expressions from {@code items} list
   * @throws IllegalArgumentException if {@code items} list is {@code null}
   */
  public static EsExpr createTuple(final List<EsExpr> items) {
    InvariantChecks.checkNotNull(items);
    if (items.isEmpty()) {
      return NIL;
    }
    if (items.size() == 1) {
      return items.get(0);
    }
    final ArrayList<EsExpr> tuple = new ArrayList<>(items);
    return new EsExpr(TUPLE_LITERAL, tuple);
  }

  /**
   * Create dotted pair for given S-expressions.
   *
   * @param lhs left expression in dotted pair
   * @param rhs right expression in dotted pair
   * @return tuple containing {@code lhs} and {@code rhs} expressions
   * @throws IllegalArgumentException if any of given expressions is {@code null}
   */
  public static EsExpr cons(final EsExpr lhs, final EsExpr rhs) {
    InvariantChecks.checkNotNull(lhs);
    InvariantChecks.checkNotNull(rhs);

    return new EsExpr(TUPLE_LITERAL, Arrays.asList(lhs, rhs));
  }
}
