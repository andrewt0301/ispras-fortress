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

import java.util.Collections;
import java.util.HashSet;
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

  public static <E> Set<E> uniteSets(Set<E> lhs, Set<E> rhs) {
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

  public static <E> Set<E> intersectSets(Set<E> lhs, Set<E> rhs) {
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
   * @return {@code true} if the sets are intersected if {@code false} otherwise. 
   * 
   * @throws NullPointerException if any of the parameters is {@code null}.
   */

  public static <E> boolean areIntersectedSets(Set<E> lhs, Set<E> rhs) {
    return intersectSets(lhs, rhs).isEmpty();
  }

  /**
   * Returns a relative complement of two sets.
   * 
   * @param lhs First set (left hand).
   * @param rhs Second set (right hand).
   * @return Relative complement of two sets.
   * 
   * @throws NullPointerException if any of the parameters is {@code null}.
   */

  public static <E> Set<E> complementSets(Set<E> lhs, Set<E> rhs) {
    checkNotNull(lhs);
    checkNotNull(rhs);

    if (lhs.isEmpty() || rhs.isEmpty()) {
      return lhs;
    }

    final Set<E> result = new HashSet<>(lhs);
    result.removeAll(rhs);

    return result;
  }

  private static void checkNotNull(Object o) {
    if (null == o) {
      throw new NullPointerException();
    }
  }
}
