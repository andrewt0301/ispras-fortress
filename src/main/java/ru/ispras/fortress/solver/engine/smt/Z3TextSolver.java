/*
 * Copyright 2011-2015 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.solver.engine.smt;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.Reader;

import ru.ispras.fortress.expression.StandardOperation;

/**
 * The Z3TextSolver class implements logic of a constraint solver that uses the Z3 tool by Microsoft
 * Research. The constraint is translated to STM-LIB code that is then saved to a file and processed
 * to the tool.
 * 
 * @author Andrei Tatarnikov
 */

public final class Z3TextSolver extends SmtTextSolver {
  private static final String NAME = "Z3 (text-based interface)";

  private static final String DESCRIPTION =
    "Solves constraints using the Z3 solver. " + 
    "Interacts with the solver via text files and command line.";

  public Z3TextSolver() {
    super(NAME, DESCRIPTION);
    initZ3Operations();
  }

  @Override
  public String getSolverPath() {
    return System.getenv("Z3_PATH");
  }

  @Override
  public Reader invokeSolver(final String path) throws IOException {
    final Process process =
        new ProcessBuilder(getSolverPath(), path).start();

    return new BufferedReader(new InputStreamReader(process.getInputStream()));
  }

  private void initZ3Operations() {
    addStandardOperation(StandardOperation.REM, "rem");
  }
}
