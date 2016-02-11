/*
 * Copyright 2016 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.logic;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.junit.Assert;
import org.junit.BeforeClass;
import org.junit.Test;

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.expression.ExprUtils;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.solver.constraint.GenericSolverTestBase;
import ru.ispras.fortress.util.InvariantChecks;

/**
 * @author <a href="mailto:smolov@ispras.ru">Sergey Smolov</a>
 */
public final class OrthogonalizerBugTestCase {
  @BeforeClass
  public static void initSolvers() {
    GenericSolverTestBase.initSolvers();
  }

  @Test
  public void runTest() {

    /* Create clauses (similar to b01) */
    final NormalForm.Builder clauses = new NormalForm.Builder(NormalForm.Type.DNF);

    final Clause.Builder clause0 = new Clause.Builder();
    clause0.add(0, false);
    clauses.add(clause0.build());

    final Clause.Builder clause1 = new Clause.Builder();
    clause1.add(1, false);
    clauses.add(clause1.build());

    final Clause.Builder clause2 = new Clause.Builder();
    clause2.add(2, false);
    clauses.add(clause2.build());

    final Clause.Builder clause3 = new Clause.Builder();
    clause3.add(3, true);
    clause3.add(4, false);
    clauses.add(clause3.build());

    final Clause.Builder clause4 = new Clause.Builder();
    clause4.add(3, true);
    clause4.add(5, false);
    clauses.add(clause4.build());

    final Clause.Builder clause5 = new Clause.Builder();
    clause5.add(3, true);
    clause5.add(6, true);
    clause5.add(7, false);
    clauses.add(clause5.build());

    final Clause.Builder clause6 = new Clause.Builder();
    clause6.add(3, true);
    clause6.add(6, true);
    clause6.add(8 ,false);
    clauses.add(clause6.build());

    final Clause.Builder clause7 = new Clause.Builder();
    clause7.add(3, true);
    clause7.add(6, true);
    clause7.add(9, true);
    clause7.add(10, false);
    clauses.add(clause7.build());

    final Clause.Builder clause8 = new Clause.Builder();
    clause8.add(3 ,true);
    clause8.add(6, true);
    clause8.add(9, true);
    clause8.add(11, false);
    clauses.add(clause8.build());

    final Clause.Builder clause9 = new Clause.Builder();
    clause9.add(3, true);
    clause9.add(6, true);
    clause9.add(9, true);
    clause9.add(12, true);
    clauses.add(clause9.build());

    final NormalForm normalForm = clauses.build();

    final Map<Integer, Node> map = new LinkedHashMap<>();
    final NodeVariable x = new NodeVariable("x", DataType.INTEGER);
    map.put(0, NodeValue.newBoolean(true));
    map.put(1, equation(x, 0));
    map.put(2, equation(x, 3));
    map.put(3, ExprUtils.getDisjunction(equation(x, 0), equation(x, 3)));
    map.put(4, equation(x, 1));
    map.put(5, equation(x, 4));
    map.put(6, ExprUtils.getDisjunction(equation(x, 1), equation(x, 4)));
    map.put(7, equation(x, 2));
    map.put(8, equation(x, 5));
    map.put(9, ExprUtils.getDisjunction(equation(x, 2), equation(x, 5)));
    map.put(10, equation(x, 6));
    map.put(11, equation(x, 7));
    map.put(12, ExprUtils.getDisjunction(equation(x, 6), equation(x, 7)));

    /* Conflicts. */
    final Set<Clause> conflicts = getConflicts(map);

    System.out.println(normalForm);
    System.out.println(conflicts);

    /* Orthogonalization. */
    final NormalForm orthForm = Orthogonalizer.orthogonalize(normalForm, conflicts);

    System.out.println(orthForm);

    final List<Clause> ortClauses = orthForm.getClauses();

    /* Reconstruct conditions from clauses. */
    final List<Node> ortNodes = getNodes(ortClauses, map);

    /* Check that conditions are mutually incompatible */
    for (int i = 0; i < ortNodes.size(); i++) {
      for (int j = 0; j < ortNodes.size(); j++) {
        if (i != j) {
          if (ExprUtils.areCompatible(ortNodes.get(i), ortNodes.get(j))) {
            System.out.println(String.format("Compatible: %d and %d", i, j));
          }

          Assert.assertFalse(ExprUtils.areCompatible(ortNodes.get(i), ortNodes.get(j)));
        }
      }
    }
  }

  private static Node equation(final NodeVariable variable, final int value) {
    return new NodeOperation(StandardOperation.EQ, variable, NodeValue.newInteger(value));
  }

  private Set<Clause> getConflicts(final Map<Integer, Node> literalMap) {

    final Set<Clause> conflicts = new LinkedHashSet<>();
    final Integer[] variables = literalMap.keySet().toArray(new Integer[]{});

    for (int i = 0; i < variables.length - 1; i++) {
      for (int j = i + 1; j < variables.length; j++) {
        final int variableI = variables[i];
        final int variableJ = variables[j];

        final Node nodeI = literalMap.get(variableI);
        final Node nodeJ = literalMap.get(variableJ);
        InvariantChecks.checkFalse(nodeI.equals(nodeJ));

        for (final boolean signI : new boolean[] {false, true}) {
          final Node signedNodeI = signI ? ExprUtils.getNegation(nodeI) : nodeI;

          for (final boolean signJ : new boolean[] {false, true}) {
            final Node signedNodeJ = signJ ? ExprUtils.getNegation(nodeJ) : nodeJ;

            if (!ExprUtils.areCompatible(signedNodeI, signedNodeJ)) {
              final Clause.Builder conflictBuilder = new Clause.Builder();

              conflictBuilder.add(variableI, signI);
              conflictBuilder.add(variableJ, signJ);

              conflicts.add(conflictBuilder.build());
            }
          }
        }
      }
    }

    return conflicts;
  }

  private List<Node> getNodes(final List<Clause> ortClauses, final Map<Integer, Node> map) {

    final List<Node> nodes = new LinkedList<>();

    for (final Clause clause : ortClauses) {

      Node node = null;

      final Set<Integer> clauseLiterals = clause.getVars();

      for (final Integer literal : clauseLiterals) {
        Node literalNode = map.get(literal);

        if (clause.getSign(literal)) {
          literalNode = ExprUtils.getNegation(literalNode);
        }
        node = node == null ? literalNode : ExprUtils.getConjunction(node, literalNode);
      }

      nodes.add(node);
    }
    return nodes;
  }
}
