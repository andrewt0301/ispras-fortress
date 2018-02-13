/*
 * Copyright 2018 ISP RAS (http://www.ispras.ru)
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
import ru.ispras.fortress.expression.Node;

public interface NodeProvider {
  /**
   * Substitutes one variable for a node expression.
   *
   * @param variable Variable to be substituted.
   * @return Node that substitutes the variable or {@code null} if no substitution is provided.
   *
   * @throws IllegalArgumentException if the argument is {@code null}.
   */
  Node getNode(Variable variable);
}
