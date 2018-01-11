/*
 * Copyright 2011-2017 ISP RAS (http://www.ispras.ru)
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

import ru.ispras.fortress.calculator.Calculator;
import ru.ispras.fortress.calculator.CalculatorEngine;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.ExprUtils;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeBinding;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.solver.Environment;
import ru.ispras.fortress.solver.Solver;
import ru.ispras.fortress.solver.SolverId;
import ru.ispras.fortress.solver.SolverResult;
import ru.ispras.fortress.solver.SolverResultChecker;
import ru.ispras.fortress.solver.xml.XMLConstraintLoader;
import ru.ispras.fortress.solver.xml.XMLConstraintSaver;
import ru.ispras.fortress.solver.xml.XMLNotLoadedException;
import ru.ispras.fortress.solver.xml.XMLNotSavedException;
import ru.ispras.fortress.transformer.ReduceOptions;
import ru.ispras.fortress.transformer.Reducer;
import ru.ispras.fortress.transformer.Transformer;

import org.junit.Assert;
import org.junit.BeforeClass;
import org.junit.Test;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static ru.ispras.fortress.solver.SolverResult.Status;

public abstract class GenericSolverTestBase {
  public static interface SampleConstraint {
    public Constraint getConstraint();
    public Iterable<Variable> getExpectedVariables();
  }

  private final SampleConstraint sample;

  public GenericSolverTestBase(SampleConstraint sample) {
    if (null == sample) {
      throw new NullPointerException();
    }

    this.sample = sample;
  }

  @BeforeClass
  public static void initSolvers() {
    final ru.ispras.fortress.solver.Solver z3Solver = SolverId.Z3_TEXT.getSolver();
    if (null == z3Solver.getSolverPath()) {
      // If the Z3_PATH environment variable is not set, we set up default solver path
      // in hope to find the the tool there.
      final String z3Path = "./tools/";
      if (Environment.isUnix()) {
        z3Solver.setSolverPath(z3Path + "z3/bin/z3");
      } else if (Environment.isWindows()) {
        z3Solver.setSolverPath(z3Path + "z3/bin/z3.exe");
      } else if (Environment.isOSX()) {
        z3Solver.setSolverPath(z3Path + "z3/bin/z3");
      } else {
        throw new UnsupportedOperationException(String.format(
          "Unsupported platform: %s.", Environment.getOSName()));
      }
    }

    final ru.ispras.fortress.solver.Solver cvc4Solver = SolverId.CVC4_TEXT.getSolver();
    if (null == cvc4Solver.getSolverPath()) {
      // If the CVC4_PATH environment variable is not set, we set up default solver path
      // in hope to find the the tool there.
      final String cvc4Path = "./tools/";
      if (Environment.isUnix()) {
        cvc4Solver.setSolverPath(cvc4Path + "cvc4-unix.bin");
      } else if (Environment.isWindows()) {
        cvc4Solver.setSolverPath(cvc4Path + "cvc4-windows.exe");
      } else {
        throw new UnsupportedOperationException(String.format(
          "Unsupported platform: %s.", Environment.getOSName()));
      }
    }
  }

  @Test
  public final void runSolverTests() {
    final Constraint constraint = sample.getConstraint();
    solveAndCheckResult(constraint);
  }

  @Test
  public final void runSerializerTests() {
    final Constraint constraint = sample.getConstraint();
    final XMLConstraintSaver saver = new XMLConstraintSaver(constraint);

    File tempFile = null;

    try {
      // Saving to and loading from file.
      tempFile = File.createTempFile(constraint.getName(), ".xml");

      final String tempFileName = tempFile.getPath();
      saver.saveToFile(tempFileName);

      final Constraint tempFileConstraint = XMLConstraintLoader.loadFromFile(tempFileName);
      ConstraintEqualityChecker.check(constraint, tempFileConstraint);

      solveAndCheckResult(tempFileConstraint);

      // Saving to and loading from string.
      final String xmlText = saver.saveToString();

      final Constraint xmlTextConstraint = XMLConstraintLoader.loadFromString(xmlText);
      ConstraintEqualityChecker.check(constraint, xmlTextConstraint);

      solveAndCheckResult(xmlTextConstraint);
    } catch (IOException e) {
      Assert.fail("Failed to create a temporary file for constraint " + constraint.getName() + ".");
    } catch (XMLNotSavedException e) {
      e.printStackTrace();
      Assert.fail(e.getMessage());
    } catch (XMLNotLoadedException e) {
      e.printStackTrace();
      Assert.fail(e.getMessage());
    } finally {
      if (null != tempFile && !Environment.isDebugMode())
        tempFile.delete();
    }
  }

  private void solveAndCheckResult(Constraint constraint) {
    String name = "unknown";
    Status globalStatus = Status.UNKNOWN;

    for (final SolverId id : SolverId.values()) {
      final Solver solver = id.getSolver();
      registerCustomOperations(solver);

      final SolverResult result = solver.solve(constraint);

      final Status localStatus = refineResult(globalStatus, result.getStatus());
      final String message =
          String.format("Mismatching solver results: %s returns %s, %s returns %s",
                        name, globalStatus,
                        solver.getName(), localStatus);

      Assert.assertTrue(message,
                        globalStatus == Status.UNKNOWN ||
                        localStatus == globalStatus);

      SolverResultChecker.checkErrors(result.getErrors());
      checkResult(getCalculator(), constraint, result);

      globalStatus = localStatus;
      name = solver.getName();
    }
  }

  private static Status refineResult(Status known, Status current) {
    if (current == Status.SAT || current == Status.UNSAT) {
      return current;
    }
    return known;
  }

  private static void checkResult(
      final CalculatorEngine calculator,
      final Constraint constraint,
      final SolverResult result) {
    final Formulas formulas = (Formulas) constraint.getInnerRep();
    final Collection<NodeVariable> variables = ExprUtils.getVariables(formulas.exprs());

    final Map<String, NodeVariable> variableMap = new HashMap<>(variables.size());
    for (final NodeVariable node : variables) {
      variableMap.put(node.getName(), node);
    }

    final List<NodeBinding.BoundVariable> bindings = new ArrayList<>(result.getVariables().size());
    for (final Variable var : result.getVariables()) {
      NodeVariable node = variableMap.get(var.getName());
      if (null == node) {
        node = new NodeVariable(constraint.findVariable(var.getName()));
      }

      final NodeValue value = new NodeValue(var.getData());
      bindings.add(NodeBinding.bindVariable(node, value));
    }

    final NodeOperation expr = new NodeOperation(StandardOperation.AND, formulas.exprs());
    final NodeBinding nodeBind = new NodeBinding(expr, bindings);
    final Node value = Transformer.substituteBinding(nodeBind);
    final Node reduced = reduceAll(calculator, value);

    Assert.assertTrue(
        String.format(
            "Calculator failed to substitute result:\n%s\n-> %s\n-> %s\n-> %s",
            expr,
            nodeBind,
            value,
            reduced),
        nodeIsTrue(reduced));
  }

  private static Node reduceAll(final CalculatorEngine calculator, final Node input) {
    Node node = null;
    Node reduced = input;
    do {
      node = reduced;
      reduced = Reducer.reduce(calculator, ReduceOptions.NEW_INSTANCE, node);
    } while (reduced != node);

    return reduced;
  }

  private static boolean nodeIsTrue(final Node node) {
    return ExprUtils.isValue(node) &&
           ExprUtils.isCondition(node) &&
           (Boolean) ((NodeValue) node).getValue();
  }

  protected CalculatorEngine getCalculator() {
    return Calculator.STANDARD;
  }

  protected void registerCustomOperations(Solver solver) {
    return;
  }
}
