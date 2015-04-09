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

package ru.ispras.fortress.solver.constraint;

import java.io.File;
import java.io.IOException;

import org.junit.Assert;
import org.junit.Test;

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
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.xml.XMLConstraintLoader;
import ru.ispras.fortress.solver.xml.XMLConstraintSaver;
import ru.ispras.fortress.solver.xml.XMLNotLoadedException;
import ru.ispras.fortress.solver.xml.XMLNotSavedException;
import ru.ispras.fortress.transformer.ReduceOptions;
import ru.ispras.fortress.transformer.Transformer;

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

    for (SolverId id : SolverId.values()) {
      if (!id.equals(SolverId.DEFAULT)) {
        final Solver solver = id.getSolver();
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
        checkResult(constraint, result);

        globalStatus = localStatus;
        name = solver.getName();
      }
    }
  }

  private static Status refineResult(Status known, Status current) {
    if (current == Status.SAT || current == Status.UNSAT) {
      return current;
    }
    return known;
  }

  private static void checkResult(Constraint constraint, SolverResult result) {
    final Formulas formulas = (Formulas) constraint.getInnerRep();
    final Collection<NodeVariable> variables =
        ExprUtils.getVariables(formulas.exprs());

    final Map<String, NodeVariable> variableMap = new HashMap<>(variables.size());
    for (NodeVariable node : variables) {
      variableMap.put(node.getName(), node);
    }
    final List<NodeBinding.BoundVariable> bindings =
        new ArrayList<>(result.getVariables().size());
    for (Variable var : result.getVariables()) {
      final NodeVariable node = variableMap.get(var.getName());
      final NodeValue value = new NodeValue(var.getData());
      bindings.add(NodeBinding.bindVariable(node, value));
    }
    final NodeOperation expr =
        new NodeOperation(StandardOperation.AND, formulas.exprs());
    final Node value = Transformer.substituteBinding(new NodeBinding(expr, bindings));
    final Node reduced = Transformer.reduce(ReduceOptions.NEW_INSTANCE, value);

    Assert.assertTrue(String.format("Calculator failed to substitute result: %s", reduced),
                      nodeIsTrue(reduced));
  }

  private static boolean nodeIsTrue(Node node) {
    return node.getKind() == Node.Kind.VALUE &&
           ExprUtils.isCondition(node) &&
           (Boolean) ((NodeValue) node).getValue();
  }
}
