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

package ru.ispras.fortress.solver.function;

import ru.ispras.fortress.data.DataType;

/**
 * The FunctionTemplate interface describes responsibilities of a function template object. A
 * function template is an object that helps create a family of similar functions that operate on
 * different argument types.
 * 
 * @author Andrei Tatarnikov
 */

public interface FunctionTemplate {
  /**
   * Returns the identifier of the operation functions instantiated from the template are associated
   * with.
   * 
   * @return Operation identifier for the instantiated functions.
   */

  Enum<?> getId();

  /**
   * Instantiates a function from the template for the given argument types.
   * 
   * @param argTypes Array of argument types.
   * @return Function for the given argument types.
   * 
   * @throws NullPointerException if the parameter equals null.
   * @throws IllegalArgumentException if the function cannot be instantiated for the given arguments
   *         (wrong number, wrong types, etc.).
   */

  Function instantiate(DataType[] argTypes);
}
