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

package ru.ispras.fortress.solver.constraint;

import ru.ispras.fortress.expression.Node;

/**
 * The ConstraintUtils class provides utility methods to deal with constraints. 
 * 
 * @author Andrei Tatarnikov
 */

public final class ConstraintUtils {
  private ConstraintUtils() {}

  /**
   * Creates a constraint from the specified expression.
   * 
   * @param expr Expression to be used as a source for the constraint.
   * @return New formula-based constraint. 
   * 
   * @throws NullPointerException if the parameter equals {@code null}.
   */

  public static Constraint newConstraint(Node expr) {
    checkNotNull(expr);

    final ConstraintBuilder builder = 
      new ConstraintBuilder(ConstraintKind.FORMULA_BASED);

    final Formulas formulas = new Formulas(expr);
    builder.setInnerRep(formulas);

    builder.addVariables(formulas.getVariables());
    return builder.build();
  }

  private static void checkNotNull(Object o) {
    if (null == o) {
      throw new NullPointerException();
    }
  }
}
