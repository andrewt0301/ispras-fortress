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

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * {@link Orthogonalizer} contains a set of utils dealing with disjunctive normal forms.
 *
 * @author <a href="mailto:kamkin@ispras.ru">Alexander Kamkin</a>
 */
public final class Orthogonalizer {
  private Orthogonalizer() {}

  /**
   * Checks whether two clauses (conjuncts), {@code lhs} and {@code rhs}, are disjoint
   * (mutually exclusive, or orthogonal).
   *
   * @param lhs the left-hand-side clause.
   * @param rhs the right-hand-side clause.
   * @return {@code true} if the clauses are disjoint; {@code false} otherwise.
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
   * Checks whether two clauses (conjuncts), {@code lhs} and {@code rhs}, are disjoint
   * (mutually exclusive, or orthogonal) w.r.t. the given set of conflicts.
   *
   * @param lhs the left-hand-side clause.
   * @param rhs the right-hand-side clause.
   * @param conflicts the set of conflicts.
   * @return {@code true} if the clauses are disjoint; {@code false} otherwise.
   */
  public static boolean areDisjoint(
      final Clause lhs,
      final Clause rhs,
      final Set<Clause> conflicts) {
    if (areDisjoint(lhs, rhs)) {
      return true;
    }

    if (conflicts == null) {
      return false;
    }

    for (final Clause conflict : conflicts) {
      final Clause.Builder clauseBuilder = new Clause.Builder();

      clauseBuilder.add(lhs);
      clauseBuilder.add(rhs);

      if (clauseBuilder.build().contains(conflict)) {
        return true;
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
  public static NormalForm orthogonalize(final NormalForm form, final Set<Clause> conflicts) {
    final List<Clause> clauses = new ArrayList<Clause>(form.getClauses());

    if (clauses.isEmpty()) {
      return new NormalForm(NormalForm.Type.DNF);
    }

    final Map<Integer, Integer> branches = new LinkedHashMap<Integer, Integer>(2 * clauses.size());
    branches.put(clauses.size() - 1, -1);

    for (int preI, i = next(branches, preI = 0); i != -1; i = next(branches, preI = i)) {
      for (int preJ, j = next(branches, preJ = -1); j != i; j = next(branches, preJ = j)) {
        final NormalForm.Builder splitBuilder = new NormalForm.Builder(NormalForm.Type.DNF);

        // Split one of the clauses to make them disjoint.
        final int index = orthogonalize(clauses.get(j), clauses.get(i), splitBuilder, conflicts);

        if (index == 0) {
          // The left-hand-side clause is rewritten (#0).
          if (replace(clauses, branches, preJ, j, splitBuilder.build())) {
            j = preJ;
          }
        } else if (index == 1) {
          // The right-hand-side clause is rewritten (#1).
          if (replace(clauses, branches, preI, i, splitBuilder.build())) {
            i = preI;
            break;
          }
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
   * Splits one of the clauses, {@code lhs} or {@code rhs}, so as to make them disjoint.
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
      final NormalForm.Builder res,
      final Set<Clause> conflicts) {
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
    final Clause.Builder factorBuilder = new Clause.Builder();

    // Iterate over the unique variables of the fixed clause.
    for (final int var : unique) {
      // One of the new clauses to be added.
      final Clause.Builder clauseBuilder = new Clause.Builder();

      clauseBuilder.add(split);

      if (prev != -1) {
        factorBuilder.add(prev, sign);
      }

      factorBuilder.add((prev = var), !(sign = fixed.getSign(var)));
      clauseBuilder.add(factorBuilder.build());

      res.add(clauseBuilder.build());
    }

    // Return the index of the split clause.
    return index;
  }

  /**
   * Replaces the i-th clause of the list with the specified set of clauses.
   *
   * @param clauses the list of clauses.
   * @param branches the next-index map.
   * @param preIndex the index of the preceding clause.
   * @param index the index of the clause to be replaced.
   * @param split the set of clauses to be substituted.
   * @return true iff the i-th clause is removed.
   */
  private static boolean replace(
      final List<Clause> clauses,
      final Map<Integer, Integer> branches,
      final int preIndex,
      final int index,
      final NormalForm split) {
    // The clause should be removed (because it is equal with another one).
    if (split.isEmpty()) {
      // The map is updated without removing the item from the list.
      branches.put(preIndex, next(branches, index));
      return true;
    }

    final List<Clause> list = split.getClauses();
    final int size = list.size();

    // The clause should be replaced with one clause.
    if (size == 1) {
      // The list item is simply updated.
      clauses.set(index, list.get(0));
      return false;
    }

    // The clause should be replaced with two or more clauses.
    final int return_i = next(branches, index);
    final int branch_i = clauses.size();

    // One of the clauses overrides the clause under processing.
    clauses.set(index, list.get(0));
    // The others are added to the end of the list.
    clauses.addAll(list.subList(1, size));

    // The map is correspondingly updated.
    branches.put(index, branch_i);
    branches.put(clauses.size() - 1, return_i);

    return false;
  }

  /**
   * Returns the index of the successive clause.
   *
   * @param branches the next-index map.
   * @param index the index of the clause.
   * @return the successive clause index.
   */
  private static int next(
      final Map<Integer, Integer> branches,
      final int index) {
    if (index == -1) {
      return 0;
    }

    final Integer j = branches.get(index);
    return (j == null ? index + 1 : j);
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
      final List<Clause> clauses) {
    final NormalForm.Builder formBuilder = new NormalForm.Builder(NormalForm.Type.DNF);

    for (int i = 0; i != -1; i = next(branches, i)) {
      formBuilder.add(clauses.get(i));
    }

    return formBuilder.build();
  }
}
