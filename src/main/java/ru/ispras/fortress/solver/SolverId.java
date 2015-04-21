/*
 * Copyright 2012-2014 ISP RAS (http://www.ispras.ru)
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

import ru.ispras.fortress.solver.engine.smt.CVC4Solver;
import ru.ispras.fortress.solver.engine.smt.Z3TextSolver;

/**
 * The SolverId enumeration specifies which solver should be used to solve a particular constraint.
 * 
 * @author Andrei Tatarnikov
 */

public enum SolverId {
  /**
   * Z3 solver by Microsoft Research. It processes a text file with SMT-LIB code and prints results
   * to the output stream.
   */

  Z3_TEXT {
    protected Solver createSolver() {
      return new Z3TextSolver();
    }
  },

  CVC4_TEXT {
    protected Solver createSolver() {
      return new CVC4Solver();
    }
  },

  /**
   * The solver which is used by default. Currently, it is Z3_TEXT.
   */

  DEFAULT {
    protected Solver createSolver() {
      return new Z3TextSolver();
    }
  };

  private Solver solver = null;

  public final Solver getSolver() {
    if (null == solver) {
      solver = createSolver();
    }

    return solver;
  }

  protected abstract Solver createSolver();
}
