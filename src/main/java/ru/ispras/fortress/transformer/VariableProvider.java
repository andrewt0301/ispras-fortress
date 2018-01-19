/*
 * Copyright 2017 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.transformer;

import ru.ispras.fortress.data.Variable;

public interface VariableProvider {
  /**
   * Substitutes one variable for another.
   *
   * @param variable Variable to be substituted.
   * @return Variable substitution or {@code null} if no substitution is provided for this variable.
   *
   * @throws IllegalArgumentException if the argument is {@code null}.
   */
  Variable getVariable(final Variable variable);
}
