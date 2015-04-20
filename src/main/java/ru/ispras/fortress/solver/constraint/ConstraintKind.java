/*
 * Copyright 2013-2014 ISP RAS (http://www.ispras.ru)
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

import ru.ispras.fortress.solver.SolverId;

/**
 * The ConstraintKind enumeration describes constraint types.
 * 
 * @author Andrei Tatarnikov
 */

public enum ConstraintKind {
  /**
   * Constant based on formula expressions (described by the Formula class and solved by the Z3_TEXT
   * solver).
   */

  FORMULA_BASED(Formulas.class, SolverId.Z3_TEXT);

  private final Class<?> innerRepClass;
  private final SolverId defaultSolverId;

  /**
   * Construct a ConstraintKind object basing on provided information.
   * 
   * @param innerRepClass Class that stores internal representation of constraints of the given
   *        type.
   * @param defaultSolverId Identifier of a solver to be used by default for constraints of the
   *        given type.
   */

  private ConstraintKind(final Class<?> innerRepClass, final SolverId defaultSolverId) {
    this.innerRepClass = innerRepClass;
    this.defaultSolverId = defaultSolverId;
  }

  /**
   * Returns the class used to describe internal representation of constraints of the given type.
   * 
   * @return Constraint internal representation class.
   */

  public Class<?> getInnerRepClass() {
    return innerRepClass;
  }

  /**
   * Returns the identifier of the solver that should be used to solve constraints of the given type
   * by default.
   * 
   * @return Solver identifier.
   */

  public SolverId getDefaultSolverId() {
    return defaultSolverId;
  }
}
