/*
 * Copyright 2011-2017 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.solver;

import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintKind;
import ru.ispras.fortress.solver.function.Function;
import ru.ispras.fortress.solver.function.FunctionTemplate;

/**
 * The {@link Solver} interface provides a protocol for working with different kinds of constraint
 * solvers in a universal way.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public interface Solver {
  /**
   * Returns the name of the solver.
   * 
   * @return Solver name.
   */
  String getName();

  /**
   * Returns the description of the solver.
   * 
   * @return solver description.
   */
  String getDescription();

  /**
   * Check whether the specified constraint kind is supported by the solver.
   * 
   * @param kind Constraint kind.
   * @return true if the constraint kind is supported or false otherwise.
   */
  boolean isSupported(ConstraintKind kind);

  /**
   * Returns true if the solver is generic and false if it is custom.
   * 
   * @return true for generic solvers or false for custom ones.
   */
  boolean isGeneric();

  /**
   * Solves the specified constraint.
   * 
   * @param constraint A constraint object.
   * @return Result of solving the constraint.
   */
  SolverResult solve(Constraint constraint);

  /**
   * Register a custom operation that extends the functionality of the solver.
   * The operation is implemented in terms of existing operations and represents a function.
   *
   * @param function Object describing the semantics and syntax of the function.
   * @return {@code true} if no such operation has been previously registered or
   *         {@code false} otherwise.
   */
  boolean addCustomOperation(Function function);

  /**
   * Register a custom operation that extends the functionality of the solver. The operation is
   * implemented in terms of existing operation and represents a family of functions derived from
   * the same template. Functions share the same logic, but may operate on different data types.
   *
   * @param template Function template that describes the semantics and syntax of a family of
   *        similar functions.
   * @return {@code true} if no such operation has been previously registered or
   *         {@code false} otherwise.
   */
  boolean addCustomOperation(FunctionTemplate template);

  /**
   * Returns the path to the external constraint solver executable used
   * by the current solver object.
   * 
   * @return Path
   */
  String getSolverPath();

  /**
   * Sets the path to the external constraint solver executable used
   * by the current solver object.
   * 
   * @param value Path
   */
  void setSolverPath(String value);
}
