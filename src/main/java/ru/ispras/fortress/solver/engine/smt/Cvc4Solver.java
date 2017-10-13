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
import java.io.SequenceInputStream;
import java.util.Collections;
import java.util.List;

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.Nodes;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.solver.function.Function;

public final class Cvc4Solver extends SmtTextSolver {
  private static final String NAME = "CVC4 (text-based interface)";

  private static final String DESCRIPTION =
      "Solves constraints using the CVC4 solver. " +
      "Interacts with the solver via text files and command line.";

  private static final String ENV_VAR_NAME = "CVC4_PATH";

  private static final String HEADER = "(set-logic QF_ABVLIRA)";

  public Cvc4Solver() {
    super(NAME, DESCRIPTION, ENV_VAR_NAME);
    initCvc4Operations();
  }

  @Override
  protected List<String> getHeader() {
    return Collections.singletonList(HEADER);
  }

  @Override
  public Reader invokeSolver(final String path) throws IOException {
    final Process process =
        new ProcessBuilder(getSolverPath(), "-mq", "--rewrite-divk", path).start();

    return new BufferedReader(
        new InputStreamReader(
            new SequenceInputStream(process.getInputStream(), process.getErrorStream())));
  }

  public static Function customRem() {
    final DataType type = DataType.INTEGER;

    final Variable lvar = new Variable("x", type);
    final Variable rvar = new Variable("y", type);

    final Node lhs = new NodeVariable(lvar);
    final Node rhs = new NodeVariable(rvar);

    final NodeOperation mod = Nodes.MOD(Nodes.ABS(lhs), Nodes.ABS(rhs));
    final NodeOperation rem =
        Nodes.ITE(
            Nodes.LESS(rhs, NodeValue.newInteger(0)),
            Nodes.MINUS(mod),
            mod);

    return new Function(StandardOperation.REM, type, rem, lvar, rvar);
  }

  public static Function customPlus() {
    final Variable var = new Variable("x", DataType.INTEGER);
    final NodeOperation plus = Nodes.ADD(new NodeVariable(var), NodeValue.newInteger(0));
    return new Function(StandardOperation.PLUS, var.getType(), plus, var);
  }

  private void initCvc4Operations() {
    addCustomOperation(customRem());
    addCustomOperation(customPlus());
    addStandardOperation(StandardOperation.BV2INT, "bv2nat");
  }
}
