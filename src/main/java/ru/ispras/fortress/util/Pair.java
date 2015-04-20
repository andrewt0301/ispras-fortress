/*
 * Copyright 2015 ISP RAS (http://www.ispras.ru)
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

public final class Pair<T, U> {
  public final T first;
  public final U second;

  public Pair(final T first, final U second) {
    checkNotNull(first);
    checkNotNull(second);

    this.first = first;
    this.second = second;
  }

  @Override
  public boolean equals(final Object obj) {
    if (this == obj) {
      return true;
    }

    if (obj == null || getClass() != obj.getClass()) {
      return false;
    }

    final Pair<?, ?> other = (Pair<?, ?>) obj;
    return first.equals(other.first) && second.equals(other.second);
  }

  @Override
  public int hashCode() {
    return 31 * first.hashCode() + second.hashCode();
  }

  @Override
  public String toString() {
    return String.format("<%s, %s>", first, second);
  }
}
