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

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * This class represents a clause, which is a set of literals.
 * 
 * @author <a href="mailto:kamkin@ispras.ru">Alexander Kamkin</a>
 */
public final class Clause {
  // / Contains the clause's literals (maps variables to negation flags).
  private final Map<Integer, Boolean> literals = new LinkedHashMap<Integer, Boolean>();

  /**
   * Constructs the empty clause.
   */
  public Clause() {}

  /**
   * Constructs a copy of the specified clause.
   * 
   * @param rhs the clause to be copied.
   */
  public Clause(final Clause rhs) {
    literals.putAll(rhs.literals);
  }

  /**
   * Checks whether the clause is empty.
   * 
   * @return true iff the clause is empty.
   */
  public boolean isEmpty() {
    return literals.isEmpty();
  }

  /**
   * Returns the number of literals in the clause.
   * 
   * @return the size of the clause.
   */
  public int size() {
    return literals.size();
  }

  /**
   * Returns the set of variables of the clause.
   * 
   * @return the variables of the clause.
   */
  public Set<Integer> getVars() {
    return literals.keySet();
  }

  /**
   * Returns the set of common variables of this clause and the specified one.
   * 
   * @param rhs the clause whose variables to be considered.
   * @return the set of common variables.
   */
  public Set<Integer> getCommonVars(final Clause rhs) {
    final Clause lhs = this;

    final Set<Integer> x = lhs.size() < rhs.size() ? lhs.getVars() : rhs.getVars();
    final Set<Integer> y = lhs.size() < rhs.size() ? rhs.getVars() : lhs.getVars();

    final Set<Integer> result = new LinkedHashSet<Integer>(x);
    result.retainAll(y);

    return result;
  }

  /**
   * Returns the set of variables of the clause that do not belong to the specified clause.
   * 
   * @param rhs the clause whose variables to be considered.
   * @return the set of unique variables.
   */
  public Set<Integer> getUniqueVars(final Clause rhs) {
    final Set<Integer> result = new LinkedHashSet<Integer>(getVars());
    result.removeAll(rhs.getVars());

    return result;
  }

  /**
   * Returns the sign of the specified variable.
   * 
   * @param var the variable.
   * @return true iff the variable is negated.
   */
  public boolean getSign(final int var) {
    return literals.get(var);
  }

  /**
   * Checks whether the clause contains the specified variable.
   * 
   * @param var the variable to be checked.
   * @return true iff the clause contains the variable.
   */
  public boolean contains(final int var) {
    return literals.containsKey(var);
  }

  /**
   * Checks whether the clause contains the specified clause.
   * 
   * @param clause the clause to be checked.
   * @return true iff the clause contains the variable.
   */
  public boolean contains(final Clause clause) {
    return literals.entrySet().containsAll(clause.literals.entrySet());
  }

  /**
   * Appends the specified literal to the clause.
   * 
   * @param var the variable.
   * @param sign the negation.
   */
  public void add(final int var, final boolean sign) {
    literals.put(var, sign);
  }

  /**
   * Appends the specified literals to the clause.
   * 
   * @param vars the variables.
   * @param sign the negation (common for all variables).
   */
  public void add(final int[] vars, final boolean sign) {
    for (int i = 0; i < vars.length; i++) {
      literals.put(vars[i], sign);
    }
  }

  /**
   * Appends the specified literals to the clause.
   * 
   * @param vars the variables.
   * @param signs the negations.
   */
  public void add(final int[] vars, final boolean[] signs) {
    assert vars.length == signs.length;

    for (int i = 0; i < vars.length; i++) {
      literals.put(vars[i], signs[i]);
    }
  }

  /**
   * Appends the specified clause to the clause.
   * 
   * @param clause the clause to be added.
   */
  public void add(final Clause clause) {
    literals.putAll(clause.literals);
  }

  /**
   * Removes the literal for the specified variable.
   * 
   * @param var the variable to be removed.
   */
  public void remove(final int var) {
    literals.remove(var);
  }

  /**
   * Removes the literals for the specified variables.
   * 
   * @param vars the variables to be removed.
   */
  public void remove(final int[] vars) {
    for (int i = 0; i < vars.length; i++) {
      literals.remove(vars[i]);
    }
  }

  /**
   * Removes the literals for the variables of the specified clause.
   * 
   * @param clause the clause whose variables to be removed.
   */
  public void remove(final Clause clause) {
    for (final int var : clause.getVars()) {
      literals.remove(var);
    }
  }

  /**
   * Removes all literals of the clause.
   */
  public void clear() {
    literals.clear();
  }
}
