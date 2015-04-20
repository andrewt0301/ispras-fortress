/*
 * Copyright 2013-2015 ISP RAS (http://www.ispras.ru)
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

import static ru.ispras.fortress.util.InvariantChecks.checkNotNull;

import java.util.ArrayList;
import java.util.List;

import ru.ispras.fortress.data.Variable;

public final class SolverResultBuilder {
  private SolverResult.Status status;
  private final List<String> errors;
  private final List<Variable> variables;

  /**
   * Constructs a SolverResultBuilder object.
   * 
   * @param status The initial status of the result.
   */

  public SolverResultBuilder(SolverResult.Status status) {
    checkNotNull(status);

    this.status = status;
    this.errors = new ArrayList<String>();
    this.variables = new ArrayList<Variable>();
  }

  /**
   * Creates a solver result object basing attributes hold by the builder.
   * 
   * @return A new solver result object.
   */

  public SolverResult build() {
    return new SolverResult(status, errors, variables);
  }

  /**
   * Sets the status of the result.
   * 
   * @param status Result status.
   */

  public void setStatus(final SolverResult.Status status) {
    this.status = status;
  }

  /**
   * Adds an error description to the list of errors.
   * 
   * @param error An error description.
   */

  public void addError(final String error) {
    errors.add(error);
  }

  /**
   * Adds a variable to the list of variables.
   * 
   * @param variable A variable object.
   */

  public void addVariable(final Variable variable) {
    variables.add(variable);
  }

  /**
   * Checks whether any errors have been registered.
   * 
   * @return {@code true} if any errors have been reported or {@code false} otherwise.
   */

  public boolean hasErrors() {
    return !errors.isEmpty();
  }
}
