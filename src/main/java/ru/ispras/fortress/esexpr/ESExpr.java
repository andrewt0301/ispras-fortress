package ru.ispras.fortress.esexpr;

import java.io.IOException;
import java.io.Reader;
import java.io.StreamTokenizer;
import java.io.StringReader;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

public final class ESExpr {
  public static final ESExpr NIL =
      new ESExpr("NIL", Collections.<ESExpr>emptyList());

  private static final String LIST_LITERAL = "<list>";
  private static final String TUPLE_LITERAL = "<tuple>";

  final String literal;
  final List<ESExpr> items;

  ESExpr(String literal, List<ESExpr> items) {
    this.literal = literal;
    this.items = items;
  }

  public boolean isAtom() {
    return items.isEmpty();
  }

  public boolean isNil() {
    return this == NIL;
  }

  public boolean isList() {
    return this.isNil() || !this.isAtom() && items.get(items.size() - 1).isNil();
  }

  public boolean isTuple() {
    return this.isNil() || !this.isAtom() && literal.equals(TUPLE_LITERAL);
  }

  public String getLiteral() {
    return literal;
  }

  public List<ESExpr> getItems() {
    return Collections.unmodifiableList(items);
  }

  public List<ESExpr> getListItems() {
    if (!this.isList()) {
      throw new UnsupportedOperationException("getListItems is defined only for S-lists");
    }
    if (this.isNil()) {
      return items;
    }
    return Collections.unmodifiableList(items.subList(0, items.size() - 1));
  }

  @Override
  public boolean equals(Object o) {
    if (o == null) {
      return false;
    }
    if (o == this) {
      return true;
    }
    if (this.getClass() != o.getClass()) {
      return false;
    }
    final ESExpr e = (ESExpr) o;
    if (e.isNil() || this.isNil() ||
        e.isAtom() != this.isAtom() ||
        e.isList() != this.isList()) {
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

  private void toString(StringBuilder builder) {
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

  private void printList(StringBuilder builder) {
    final String delim = " ";
    for (int i = 0; i < items.size() - 1; ++i) {
      items.get(i).toString(builder);
      builder.append(delim);
    }
    builder.delete(builder.length() - delim.length(), builder.length());
  }

  private void printTuple(StringBuilder builder) {
    final String delim = " . ";
    for (ESExpr e : items) {
      e.toString(builder);
      builder.append(delim);
    }
    builder.delete(builder.length() - delim.length(), builder.length());
  }

  public ESExpr normalizeLists() {
    if (this.isAtom()) {
      return this;
    }
    final ArrayList<ESExpr> normItems = new ArrayList<>(items.size());
    boolean update = false;
    for (ESExpr e : items) {
      final ESExpr norm = e.normalizeLists();
      normItems.add(norm);
      update = update || norm != e;
    }
    final ESExpr last = normItems.get(normItems.size() - 1);
    if (this.isTuple() && last.isList() && !last.isNil()) {
      normItems.remove(normItems.size() - 1);
      normItems.addAll(last.getItems());
      update = true;
    }
    if (!update) {
      return this;
    }
    normItems.trimToSize();
    return new ESExpr(LIST_LITERAL, normItems);
  }

  public ESExpr normalizePairs() {
    if (this.isAtom()) {
      return this;
    }
    if (this.items.size() == 2) {
      final ESExpr lhs = items.get(0).normalizePairs();
      final ESExpr rhs = items.get(1).normalizePairs();
      if (lhs == items.get(0) && rhs == items.get(1)) {
        return this;
      }
      return cons(lhs, rhs);
    }
    ESExpr last = items.get(items.size() - 1).normalizePairs();
    for (int i = items.size() - 2; i >= 0; --i) {
      last = cons(items.get(i).normalizePairs(), last);
    }
    return last;
  }

  public static ESExpr createAtom(String literal) {
    notnull(literal);
    if (literal.toUpperCase().equals(NIL.getLiteral())) {
      return NIL;
    }
    return new ESExpr(literal, Collections.<ESExpr>emptyList());
  }

  public static ESExpr createList(List<ESExpr> items) {
    notnull(items);
    if (items.isEmpty()) {
      return NIL;
    }
    final ArrayList<ESExpr> list = new ArrayList<>(items.size() + 1);
    list.addAll(items);
    list.add(NIL);
    return new ESExpr(LIST_LITERAL, list);
  }

  public static ESExpr createTuple(List<ESExpr> items) {
    notnull(items);
    if (items.isEmpty()) {
      return NIL;
    }
    if (items.size() == 1) {
      return items.get(0);
    }
    final ArrayList<ESExpr> tuple = new ArrayList<>(items);
    return new ESExpr(TUPLE_LITERAL, tuple);
  }

  public static ESExpr cons(ESExpr lhs, ESExpr rhs) {
    notnull(lhs);
    notnull(rhs);

    return new ESExpr(TUPLE_LITERAL, Arrays.asList(lhs, rhs));
  }

  private static void notnull(Object o) {
    if (o == null) {
      throw new NullPointerException();
    }
  }
}
