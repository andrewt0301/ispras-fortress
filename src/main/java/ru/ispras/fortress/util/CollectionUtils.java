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

package ru.ispras.fortress.util;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * The {@link CollectionUtils} class provides static utility methods for working with collections.
 *
 * <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public final class CollectionUtils {
  private CollectionUtils() {}

  /**
   * Returns a union of two sets.
   *
   * @param lhs First set (left hand).
   * @param rhs Second set (right hand).
   * @param <E> Set element type.
   * @return Union of two sets.
   *
   * @throws IllegalArgumentException if any of the parameters is {@code null}.
   */
  public static <E> Set<E> uniteSets(final Set<E> lhs, final Set<E> rhs) {
    InvariantChecks.checkNotNull(lhs);
    InvariantChecks.checkNotNull(rhs);

    if (lhs.isEmpty()) {
      return rhs;
    }

    if (rhs.isEmpty()) {
      return lhs;
    }

    final Set<E> result = new HashSet<>(lhs);
    result.addAll(rhs);

    return result;
  }

  /**
   * Returns an intersection of two sets.
   *
   * @param lhs First set (left hand).
   * @param rhs Second set (right hand).
   * @param <E> Set element type.
   * @return Intersection of two sets.
   *
   * @throws IllegalArgumentException if any of the parameters is {@code null}.
   */
  public static <E> Set<E> intersectSets(final Set<E> lhs, final Set<E> rhs) {
    InvariantChecks.checkNotNull(lhs);
    InvariantChecks.checkNotNull(rhs);

    if (lhs.isEmpty() || rhs.isEmpty()) {
      return Collections.emptySet();
    }

    final Set<E> result = new HashSet<>(lhs);
    result.retainAll(rhs);

    return result;
  }

  /**
   * Checks whether two sets are intersected (have as non-empty intersection).
   *
   * @param lhs First set (left hand).
   * @param rhs Second set (right hand).
   * @param <E> Set element type.
   * @return {@code true} if the sets are intersected, {@code false} otherwise.
   *
   * @throws IllegalArgumentException if any of the parameters is {@code null}.
   */
  public static <E> boolean areIntersectedSets(final Set<E> lhs, final Set<E> rhs) {
    return !intersectSets(lhs, rhs).isEmpty();
  }

  /**
   * Returns a relative complement of two sets.
   *
   * @param lhs First set (left hand).
   * @param rhs Second set (right hand).
   * @param <E> Set element type.
   * @return Relative complement of two sets.
   *
   * @throws IllegalArgumentException if any of the parameters is {@code null}.
   */
  public static <E> Set<E> complementSets(final Set<E> lhs, final Set<E> rhs) {
    InvariantChecks.checkNotNull(lhs);
    InvariantChecks.checkNotNull(rhs);

    if (lhs.isEmpty() || rhs.isEmpty()) {
      return lhs;
    }

    final Set<E> result = new HashSet<>(lhs);
    result.removeAll(rhs);

    return result;
  }

  /**
   * Appends all elements from the specified list to another list and
   * returns the updated list with the appended elements.
   *
   * @param first List to which the elements will be appended.
   * @param second List which contains elements to be appended.
   * @param <T> List element type.
   * @return Updated list that contains the appended elements.
   *
   * @throws IllegalArgumentException if any of the arguments is {@code null}.
   */
  public static <T> List<T> appendToList(final List<T> first, final List<T> second) {
    InvariantChecks.checkNotNull(first);
    InvariantChecks.checkNotNull(second);

    if (second.isEmpty()) {
      return first;
    }

    if (first.isEmpty()) {
      return new ArrayList<T>(second);
    }

    first.addAll(second);
    return first;
  }

  /**
   * Appends the specified element to the specified list and returns
   * the updated list with the appended element.
   *
   * @param list List to which the element will be appended.
   * @param element Element to be added.
   * @param <T> List element type.
   * @return Updated list that contains the appended element.
   *
   * @throws IllegalArgumentException if the {@code list} argument is {@code null}.
   */
  public static <T> List<T> appendToList(final List<T> list, final T element) {
    InvariantChecks.checkNotNull(list);

    final List<T> result = list.isEmpty() ? new ArrayList<T>() : list;
    result.add(element);

    return result;
  }

  /**
   * Merges two lists two lists. Returns a new list that contains elements of both lists.
   * If any of the lists is empty, returns the other list.
   *
   * @param first First list to be merged.
   * @param second Second list to be merged.
   * @param <T> List element type.
   * @return Merged list.
   *
   * @throws IllegalArgumentException if any of the arguments is {@code null}.
   */
  public static <T> List<T> mergeLists(final List<T> first, final List<T> second) {
    InvariantChecks.checkNotNull(first);
    InvariantChecks.checkNotNull(second);

    if (first.isEmpty()) {
      return second;
    }

    if (second.isEmpty()) {
      return first;
    }

    final List<T> result = new ArrayList<>(first.size() + second.size());

    result.addAll(first);
    result.addAll(second);

    return result;
  }
}
