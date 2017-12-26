/*
 * Copyright 2014-2017 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.solver.constraint;

import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.solver.Solver;
import ru.ispras.fortress.solver.SolverId;
import ru.ispras.fortress.solver.SolverResult;
import ru.ispras.fortress.util.InvariantChecks;

import java.util.Collection;
import java.util.Collections;

/**
 * The ConstraintUtils class provides utility methods to deal with constraints.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public final class ConstraintUtils {
  private ConstraintUtils() {}

  /**
   * Creates a constraint from the specified expression.
   *
   * @param e Expression to be used as a source for the constraint.
   * @return New formula-based constraint.
   *
   * @throws IllegalArgumentException if the parameter equals {@code null}.
   */
  public static Constraint newConstraint(final Node e) {
    InvariantChecks.checkNotNull(e);
    return newConstraint(Collections.singleton(e));
  }

  public static Constraint newConstraint(final Collection<? extends Node> formulae) {
    InvariantChecks.checkNotNull(formulae);

    final ConstraintBuilder builder =
        new ConstraintBuilder(ConstraintKind.FORMULA_BASED);

    final Formulas formulas = new Formulas();
    formulas.addAll(formulae);

    builder.setInnerRep(formulas);
    builder.addVariables(formulas.getVariables());

    return builder.build();
  }

  /**
   * Solves the specified constraint with the solver specified as default
   * for the given constraint kind.
   *
   * @param constraint Constraint to be solved.
   * @return Result of solving the constraint.
   *
   * @throws IllegalArgumentException if the parameter equals {@code null}.
   */
  public static SolverResult solve(final Constraint constraint) {
    InvariantChecks.checkNotNull(constraint);

    final SolverId solverId = constraint.getKind().getDefaultSolverId();
    final Solver solver = solverId.getSolver();

    return solver.solve(constraint);
  }
}
