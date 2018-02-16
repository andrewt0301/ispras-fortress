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

package ru.ispras.fortress.logic;

import ru.ispras.fortress.util.InvariantChecks;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * This class represents a normal form, which is a set of clauses. The representation can be
 * interpreted as either DNF or CNF.
 *
 * @author <a href="mailto:kamkin@ispras.ru">Alexander Kamkin</a>
 */
public final class NormalForm {
  /**
   * This enumeration contains the type of the normal form.
   */
  public enum Type {
    /** Disjunctive normal form (DNF). */
    DNF,
    /** Conjunctive normal form (CNF). */
    CNF
  }

  /**
   * {@link Builder} implements a clause builder.
   */
  public static final class Builder {
    /** The type of the normal form. */
    private final Type type;
    /** Contains the clauses of the normal form. */
    private final List<Clause> clauses = new ArrayList<>();

    public Builder(final Type type) {
      InvariantChecks.checkNotNull(type);
      this.type = type;
    }

    /**
     * Appends the specified clause to the normal form.
     *
     * @param clause the clause to be added.
     */
    public void add(final Clause clause) {
      InvariantChecks.checkNotNull(clause);
      clauses.add(clause);
    }

    /**
     * Appends the clauses of the normal form specified as a parameter to this normal form.
     *
     * @param form the form whose clauses to be added.
     */
    public void add(final NormalForm form) {
      InvariantChecks.checkNotNull(form);
      clauses.addAll(form.clauses);
    }

    public NormalForm build() {
      return new NormalForm(type, clauses);
    }
  }

  /** The type of the normal form. */
  private final Type type;
  /** Contains the clauses of the normal form. */
  private final List<Clause> clauses;

  /**
   * Constructs the normal form of the specified type consisting of the specified clauses.
   *
   * @param type the type of the form.
   * @param clauses the clauses of the form.
   */
  public NormalForm(final Type type, final Collection<Clause> clauses) {
    InvariantChecks.checkNotNull(type);
    InvariantChecks.checkNotNull(clauses);

    this.type = type;
    this.clauses = new ArrayList<Clause>(clauses);
  }

  /**
   * Constructs the empty normal form of the specified type.
   *
   * @param type the type of the form.
   */
  public NormalForm(final Type type) {
    this(type, new ArrayList<Clause>());
  }


  /**
   * Returns the type of the normal form ({@code DNF} or {@code CNF}).
   *
   * @return the type of the form.
   */
  public Type getType() {
    return type;
  }

  /**
   * Checks whether the normal form is empty.
   *
   * @return {@code true} if the normal form is empty; {@code false} otherwise.
   */
  public boolean isEmpty() {
    return clauses.isEmpty();
  }

  /**
   * Returns the number of clauses in the normal form.
   *
   * @return the size of the form.
   */
  public int size() {
    return clauses.size();
  }

  /**
   * Returns the clauses of the normal form.
   *
   * @return the clauses of the form.
   */
  public List<Clause> getClauses() {
    return clauses;
  }

  /**
   * Returns the string representation of the normal form.
   *
   * @return the string representing the form.
   */
  public String toString() {
    final String extOp = type == Type.DNF ? " | " : " & ";
    final String intOp = type == Type.DNF ? " & " : " | ";

    final StringBuffer buffer = new StringBuffer();

    boolean extSign = false;
    for (final Clause clause : clauses) {
      if (extSign) {
        buffer.append(extOp);
      }
      extSign = true;

      buffer.append(clause.toString(intOp));
    }

    return buffer.toString();
  }
}
