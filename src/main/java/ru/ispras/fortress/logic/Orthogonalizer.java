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

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * This class contains a set of utils dealing with disjunctive normal forms.
 * 
 * @author <a href="mailto:kamkin@ispras.ru">Alexander Kamkin</a>
 */
public final class Orthogonalizer {
  private Orthogonalizer() {}
  
  /**
   * Checks whether two clauses (conjuncts), <code>lhs</code> and <code>rhs</code>, are disjoint
   * (mutually exclusive or orthogonal).
   * 
   * @param lhs the left-hand-side clause.
   * @param rhs the right-hand-side clause.
   * @return <code>true</code> if the clauses are disjoint; <code>false</code> otherwise.
   */
  public static boolean areDisjoint(final Clause lhs, final Clause rhs) {
    final Set<Integer> common = lhs.getCommonVars(rhs);

    // Iterate over all common variables.
    for (final int var : common) {
      // For each of them check whether it occurs with different signs.
      if (lhs.getSign(var) != rhs.getSign(var)) {
        return true;
      }
    }

    return false;
  }

  /**
   * Checks whether two clauses (conjuncts), <code>lhs</code> and <code>rhs</code>, are disjoint
   * (mutually exclusive or orthogonal) w.r.t. the given set of conflicts.
   * 
   * @param lhs the left-hand-side clause.
   * @param rhs the right-hand-side clause.
   * @param conflicts the set of conflicts.
   * @return <code>true</code> if the clauses are disjoint; <code>false</code> otherwise.
   */
  public static boolean areDisjoint(final Clause lhs, final Clause rhs,
      final Set<Conflict> conflicts) {
    if (areDisjoint(lhs, rhs)) {
      return true;
    }

    if (conflicts == null) {
      return false;
    }

    for (final Conflict conflict : conflicts) {
      final int var1 = conflict.getLhsVar();
      final int var2 = conflict.getRhsVar();

      final boolean neg = conflict.areDifferentSigns();

      if (lhs.contains(var1) && rhs.contains(var2)) {
        if ((lhs.getSign(var1) != rhs.getSign(var2)) == neg) {
          return true;
        }
      } else if (lhs.contains(var2) && rhs.contains(var1)) {
        if ((lhs.getSign(var2) != rhs.getSign(var1)) == neg) {
          return true;
        }
      }
    }

    return false;
  }

  /**
   * Orthogonalizes the specified DNF, i.e. constructs an equivalent DNF consisting of disjoint
   * clauses.
   * 
   * @param form the DNF to be orthogonalized.
   * @param conflicts the set of conflicts.
   * @return the orthogonal DNF equivalent to the specified one.
   */
  public static NormalForm orthogonalize(final NormalForm form, final Set<Conflict> conflicts) {
    final ArrayList<Clause> clauses = new ArrayList<Clause>(form.getClauses());

    if (clauses.isEmpty()) {
      return new NormalForm(NormalForm.Type.DNF);
    }

    final Map<Integer, Integer> branches = new LinkedHashMap<Integer, Integer>(2 * clauses.size());
    branches.put(clauses.size() - 1, -1);

    for (int pre_i, i = next(branches, pre_i = 0); i != -1; i = next(branches, pre_i = i))
      for (int pre_j, j = next(branches, pre_j = -1); j != i; j = next(branches, pre_j = j)) {
        final NormalForm split = new NormalForm(NormalForm.Type.DNF);

        // Split one of the clauses to make them disjoint.
        int index = orthogonalize(clauses.get(j), clauses.get(i), split, conflicts);

        // The left-hand-side clause is rewritten (#0).
        if (index == 0) {
          if (replace(clauses, branches, pre_j, j, split)) {
            j = pre_j;
          }
        }
        // The right-hand-side clause is rewritten (#1).
        else if (index == 1) {
          if (replace(clauses, branches, pre_i, i, split)) {
            i = pre_i;
            break;
          }
        }
      }

    return construct(branches, clauses);
  }

  /**
   * Orthogonalizes the specified DNF, i.e. constructs an equivalent DNF consisting of disjoint
   * clauses.
   * 
   * @param form the DNF to be orthogonalized.
   * @return the orthogonal DNF equivalent to the specified one.
   */
  public static NormalForm orthogonalize(final NormalForm form) {
    return orthogonalize(form, /* No conflicts */null);
  }

  /**
   * Splits one of the clauses, <code>lhs</code> or <code>rhs</code>, so as to make them disjoint.
   * 
   * @param lhs the left-hand-side clause.
   * @param rhs the right-hand-side clause.
   * @param res the splitting result.
   * @param conflicts the set of conflicts.
   * @return the index of the split clause or -1 if no one has been split.
   */
  private static int orthogonalize(
      final Clause lhs,
      final Clause rhs,
      final NormalForm res,
      final Set<Conflict> conflicts) {
    // The specified clauses are disjoint.
    if (areDisjoint(lhs, rhs, conflicts)) {
      return -1;
    }

    // Try to split the left-hand-side clause (#0).
    // Splitting the left-hand-side clause is preferable.
    int index = 0;
    // To do it, the right-hand-side clause should have unique variables.
    Set<Integer> unique = rhs.getUniqueVars(lhs);

    // If it does not.
    if (unique.isEmpty()) {
      // Try to split the right-hand-side clause (#1).
      index = 1;
      // To do it, the left-hand-side clause should have unique variables.
      unique = lhs.getUniqueVars(rhs);

      // If it does not, the clauses are equal.
      if (unique.isEmpty()) {
        // The right-hand-side clause is removed (#1).
        return 1;
      }
    }

    // One of the clauses is fixed (the other one is split).
    final Clause fixed = (index == 1 ? lhs : rhs);
    final Clause split = (index == 1 ? rhs : lhs);

    int prev = -1;
    boolean sign = false;

    // Additional literals to be added to the splitting clause.
    Clause factor = new Clause();

    // Iterate over the unique variables of the fixed clause.
    for (final int var : unique) {
      // One of the new clauses to be added.
      Clause clause = new Clause(split);

      if (prev != -1) {
        factor.add(prev, sign);
      }

      factor.add((prev = var), !(sign = fixed.getSign(var)));
      clause.add(factor);

      res.add(clause);
    }

    // Return the index of the split clause.
    return index;
  }

  /**
   * Replaces the i-th clause of the list with the specified set of clauses.
   * 
   * @param clauses the list of clauses.
   * @param branches the next-index map.
   * @param pre_i the index of the preceding clause.
   * @param i the index of the clause to be replaced.
   * @param split the set of clauses to be substituted.
   * @return true iff the i-th clause is removed.
   */
  private static boolean replace(
      final ArrayList<Clause> clauses,
      final Map<Integer, Integer> branches,
      final int pre_i,
      final int i,
      final NormalForm split) {
    // The clause should be removed (because it is equal with another one).
    if (split.isEmpty()) {
      // The map is updated without removing the item from the list.
      branches.put(pre_i, next(branches, i));
      return true;
    }

    final List<Clause> list = split.getClauses();
    final int size = list.size();

    // The clause should be replaced with one clause.
    if (size == 1) {
      // The list item is simply updated.
      clauses.set(i, list.get(0));
      return false;
    }

    // The clause should be replaced with two or more clauses.
    final int return_i = next(branches, i);
    final int branch_i = clauses.size();

    // One of the clauses overrides the clause under processing.
    clauses.set(i, list.get(0));
    // The others are added to the end of the list.
    clauses.addAll(list.subList(1, size));

    // The map is correspondingly updated.
    branches.put(i, branch_i);
    branches.put(clauses.size() - 1, return_i);

    return false;
  }

  /**
   * Returns the index of the successive clause.
   * 
   * @param branches the next-index map.
   * @param i the index of the clause.
   * @return the successive clause index.
   */
  private static int next(
      final Map<Integer, Integer> branches,
      final int i) {
    if (i == -1) {
      return 0;
    }

    final Integer j = branches.get(i);
    return (j == null ? i + 1 : j);
  }

  /**
   * Traverses the list of clauses and constructs the DNF.
   * 
   * @param branches the next-index map.
   * @param clauses the list of clauses.
   * @return the DNF.
   */
  private static NormalForm construct(
      final Map<Integer, Integer> branches,
      final ArrayList<Clause> clauses) {
    final NormalForm form = new NormalForm(NormalForm.Type.DNF);

    for (int i = 0; i != -1; i = next(branches, i)) {
      form.add(clauses.get(i));
    }

    return form;
  }
}
