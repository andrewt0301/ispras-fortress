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

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.Variable;

/**
 * {@link ValueProvider} class provides variable values to be used for expression reduction.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public interface ValueProvider {
  /**
   * Returns value of the specified variable.
   *
   * @param variable Variable to be substituted with a value.
   * @return Variable value or {@code null} if no value is provided for this variable.
   *
   * @throws IllegalArgumentException if the argument is {@code null}.
   */
  Data getVariableValue(final Variable variable);
}
