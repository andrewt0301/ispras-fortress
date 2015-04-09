/*
 * Copyright 2011-2014 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.solver.engine.cvc4;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.Reader;

import ru.ispras.fortress.solver.engine.smt.SmtTextSolver;

public final class CVC4Solver extends SmtTextSolver {
  private static final String NAME = "CVC4 (text-based interface)";

  private static final String DESCRIPTION =
    "Solves constraints using the CVC4 solver. " + 
    "Interacts with the solver via text files and command line.";

  public CVC4Solver() {
    super(NAME, DESCRIPTION);
  }

  @Override
  public String getSolverPath() {
    return Environment.getSolverPath();
  }

  @Override
  public Reader invokeSolver(String path) throws IOException {
    final Process process =
        new ProcessBuilder(getSolverPath(), "-m", path).start();

    final BufferedReader reader = 
        new BufferedReader(new InputStreamReader(process.getInputStream()));

    return reader;
  }
}
