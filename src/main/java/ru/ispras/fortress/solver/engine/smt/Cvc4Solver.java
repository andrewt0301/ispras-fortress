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

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.solver.function.Function;

public final class Cvc4Solver extends SmtTextSolver {
  private static final String NAME = "CVC4 (text-based interface)";

  private static final String DESCRIPTION =
    "Solves constraints using the CVC4 solver. " + 
    "Interacts with the solver via text files and command line.";

  public Cvc4Solver() {
    super(NAME, DESCRIPTION);
    addCustomOperation(customRem());
    addCustomOperation(customPlus());
  }

  @Override
  public String getSolverPath() {
    return System.getenv("CVC4_PATH");
  }

  @Override
  public Reader invokeSolver(final String path) throws IOException {
    final Process process =
        new ProcessBuilder(getSolverPath(), "-m", path).start();

    return new BufferedReader(new InputStreamReader(process.getInputStream()));
  }

  public static Function customRem() {
    final DataType type = DataType.INTEGER;

    final Variable lvar = new Variable("x", type);
    final Variable rvar = new Variable("y", type);

    final Node lhs = new NodeVariable(lvar);
    final Node rhs = new NodeVariable(rvar);

    final NodeOperation mod =
        new NodeOperation(StandardOperation.MOD,
                          new NodeOperation(StandardOperation.ABS, lhs),
                          new NodeOperation(StandardOperation.ABS, rhs));
    final NodeOperation rem =
        new NodeOperation(StandardOperation.ITE,
                          new NodeOperation(StandardOperation.LESS, rhs, NodeValue.newInteger(0)),
                          new NodeOperation(StandardOperation.MINUS, mod),
                          mod);

    return new Function(StandardOperation.REM, type, rem, lvar, rvar);
  }

  public static Function customPlus() {
    final Variable var = new Variable("x", DataType.INTEGER);
    final NodeOperation plus = new NodeOperation(StandardOperation.ADD,
                                                 new NodeVariable(var),
                                                 NodeValue.newInteger(0));
    return new Function(StandardOperation.PLUS, var.getType(), plus, var);
  }
}
