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

package ru.ispras.fortress.util;

import static ru.ispras.fortress.util.InvariantChecks.checkNotNull;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * The CollectionUtils class provides static utility methods for
 * working with collections.
 * 
 * @author Andrei Tatarnikov
 */

public final class CollectionUtils {
  
  private CollectionUtils() {}

  /**
   * Returns a union of two sets.
   * 
   * @param lhs First set (left hand).
   * @param rhs Second set (right hand).
   * @return Union of two sets.
   * 
   * @throws NullPointerException if any of the parameters is {@code null}.
   */

  public static <E> Set<E> uniteSets(final Set<E> lhs, final Set<E> rhs) {
    checkNotNull(lhs);
    checkNotNull(rhs);

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
   * @return Intersection of two sets.
   * 
   * @throws NullPointerException if any of the parameters is {@code null}.
   */

  public static <E> Set<E> intersectSets(final Set<E> lhs, final Set<E> rhs) {
    checkNotNull(lhs);
    checkNotNull(rhs);
    
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
   * @return {@code true} if the sets are intersected, {@code false} otherwise.
   * 
   * @throws NullPointerException if any of the parameters is {@code null}.
   */

  public static <E> boolean areIntersectedSets(final Set<E> lhs, final Set<E> rhs) {
    return !intersectSets(lhs, rhs).isEmpty();
  }

  /**
   * Returns a relative complement of two sets.
   * 
   * @param lhs First set (left hand).
   * @param rhs Second set (right hand).
   * @return Relative complement of two sets.
   * 
   * @throws IllegalArgumentException if any of the parameters is {@code null}.
   */

  public static <E> Set<E> complementSets(final Set<E> lhs, final Set<E> rhs) {
    checkNotNull(lhs);
    checkNotNull(rhs);

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
   * @param lhs List to which the elements will be appended.
   * @param rhs List which contains elements to be appended. 
   * @return Updated list that contains the appended elements.
   * 
   * @throws IllegalArgumentException if any of the parameters is {@code null}.
   */

  public static <T> List<T> appendToList(final List<T> lhs, final List<T> rhs) {
    checkNotNull(lhs);
    checkNotNull(rhs);

    if (rhs.isEmpty()) {
      return lhs;
    }

    if (lhs.isEmpty()) {
      return new ArrayList<T>(rhs);
    }

    lhs.addAll(rhs);
    return lhs;
  }

  /**
   * Appends the specified element to the specified list and returns
   * the updated list with the appended element.
   * 
   * @param lhs List to which the element will be appended.
   * @param elem Element to be added. 
   * @return Updated list that contains the appended element.
   * 
   * @throws IllegalArgumentException if the {@code lhs} parameter is {@code null}.
   */

  public static <T> List<T> appendToList(final List<T> lhs, final T elem) {
    checkNotNull(lhs);

    final List<T> result = lhs.isEmpty() ? new ArrayList<T>() : lhs;
    result.add(elem);

    return lhs;
  }
}
