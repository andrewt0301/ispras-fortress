/*
 * Copyright 2012-2018 ISP RAS (http://www.ispras.ru)
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

import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.util.InvariantChecks;
import ru.ispras.fortress.util.Result;

import java.util.List;

/**
 * The {@link SolverResult} class stores a solution to the specified constraint
 * including the status of the operation and the list of errors if any occurred.
 * 
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public final class SolverResult extends Result<SolverResult.Status, List<Variable>> {
  /**
   * Describes possible statuses of the results produced by a constraint solver.
   * 
   * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
   */
  public static enum Status {
    /** Solution is found */
    SAT,
    /** No solution exists */
    UNSAT,
    /** Failed to find a solution (e.g. limitation of the current solver) */
    UNKNOWN,
    /** An error occurred */
    ERROR
  }

  /**
   * Constructs for a solver result object basing on specified attributes.
   * 
   * @param status Status of the result.
   * @param errors List of errors.
   * @param variables List of variables.
   * 
   * @throws IllegalArgumentException if any of the parameters equals {@code null}.
   */
  public SolverResult(
      final Status status,
      final List<String> errors,
      final List<Variable> variables) {
    super(status, variables, errors);
    InvariantChecks.checkNotNull(variables);
  }

  /**
   * Returns the list of variables that store a solution to a constraint.
   * 
   * @return The list of output variables.
   */
  public List<Variable> getVariables() {
    return getResult();
  }

  @Override
  public String toString() {
    return String.format(
        "SolverResult [status=%s, errors=%s, variables=%s]",
        getStatus(),
        getErrors(),
        getVariables()
        );
  }
}
