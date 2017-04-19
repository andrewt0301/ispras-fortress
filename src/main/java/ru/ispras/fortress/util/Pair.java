/*
 * Copyright 2015-2017 ISP RAS (http://www.ispras.ru)
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

public final class Pair<T, U> {
  public final T first;
  public final U second;

  public Pair(final T first, final U second) {
    this.first = first;
    this.second = second;
  }

  @Override
  public int hashCode() {
    final int prime = 31;
    int result = 1;
    result = prime * result + ((first == null) ? 0 : first.hashCode());
    result = prime * result + ((second == null) ? 0 : second.hashCode());
    return result;
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
    return equals(this.first, other.first) &&
           equals(this.second, other.second);
  }

  private static boolean equals(final Object thisObject, final Object otherObject) {
    return thisObject == null ?
           thisObject == otherObject :
           thisObject.equals(otherObject);
  }

  @Override
  public String toString() {
    return String.format("<%s, %s>", first, second);
  }
}
