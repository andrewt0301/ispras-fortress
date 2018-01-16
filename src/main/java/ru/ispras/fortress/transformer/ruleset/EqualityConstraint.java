/*
 * Copyright 2015 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.transformer.ruleset;

import static ru.ispras.fortress.util.InvariantChecks.checkNotNull;
import static ru.ispras.fortress.util.InvariantChecks.checkTrue;

import ru.ispras.fortress.expression.ExprUtils;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.Nodes;
import ru.ispras.fortress.expression.StandardOperation;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

class EqualityConstraint {
  private final Map<Node, EqualityGroup> equalLinks;
  private final List<EqualityGroup> equalityGroups;
  private final List<NodeOperation> inequalities;

  private boolean evaluated;
  private boolean consistent;

  public EqualityConstraint() {
    this.equalLinks = new HashMap<>();
    this.equalityGroups = new ArrayList<>();
    this.inequalities = new ArrayList<>();

    this.evaluateTo(true);
  }

  public boolean isEmpty() {
    return equalityGroups.isEmpty() && inequalities.isEmpty();
  }

  public void addEquality(final Node node) {
    checkNotNull(node);
    checkTrue(ExprUtils.isOperation(node, StandardOperation.EQ));

    if (this.hasKnownConflict()) {
      return;
    }
    final NodeOperation eq = (NodeOperation) node;
    final List<EqualityGroup> groups = new ArrayList<>(eq.getOperandCount());
    final List<Node> orphaned = new ArrayList<>();

    for (int i = 0; i < eq.getOperandCount(); ++i) {
      final Node operand = eq.getOperand(i);
      if (equalLinks.containsKey(operand)) {
        final EqualityGroup group = equalLinks.get(operand);
        if (!groups.contains(group)) {
          groups.add(equalLinks.get(operand));
        }
      } else {
        orphaned.add(operand);
      }
    }

    final EqualityGroup equalGroup = mergeGroupsAdd(groups, orphaned);
    if (equalGroup == null) {
      this.evaluated = true;
      this.consistent = false;
      return;
    }

    equalityGroups.removeAll(groups);
    equalityGroups.add(equalGroup);
    updateGroupLinks(equalGroup);

    this.evaluated = this.inequalities.isEmpty();
    this.consistent = true;
  }

  private void updateGroupLinks(final EqualityGroup group) {
    for (final Node node : group.variables) {
      equalLinks.put(node, group);
    }
    for (final Node node : group.constants) {
      equalLinks.put(node, group);
    }
    for (final Node node : group.remains) {
      equalLinks.put(node, group);
    }
  }

  private EqualityGroup mergeGroupsAdd(
      final Collection<EqualityGroup> groups,
      final Collection<? extends Node> nodes) {
    final EqualityGroup merged = new EqualityGroup();
    for (final EqualityGroup group : groups) {
      merged.constants.addAll(group.constants);
    }
    merged.addAll(nodes);
    if (merged.constants.size() > 1) {
      return null;
    }

    for (final EqualityGroup group : groups) {
      merged.variables.addAll(group.variables);
      merged.remains.addAll(group.remains);
    }
    return merged;
  }

  public void addInequality(Node node) {
    checkNotNull(node);
    checkTrue(ExprUtils.isOperation(node, StandardOperation.NOTEQ));

    if (this.hasKnownConflict()) {
      return;
    }
    final NodeOperation noteq = (NodeOperation) node;
    if (!inequalities.contains(noteq)) {
      inequalities.add(noteq);
      this.evaluated = false;
    }
  }

  private boolean hasKnownConflict() {
    return this.evaluated && !this.consistent;
  }

  private boolean evaluateTo(boolean value) {
    this.evaluated = true;
    this.consistent = value;

    return value;
  }

  private boolean checkConsistency() {
    if (this.evaluated) {
      return this.consistent;
    }
    final List<Node> operands = new ArrayList<>();
    for (final NodeOperation noteq : inequalities) {
      operands.addAll(noteq.getOperands());
      for (int i = 0; i < operands.size() - 1; ++i) {
        if (!isNotEqual(operands.get(i), operands.subList(i + 1, operands.size()))) {
          return evaluateTo(false);
        }
      }
      operands.clear();
    }
    return evaluateTo(true);
  }

  private boolean isNotEqual(
      final Node item, 
      final Collection<? extends Node> inequal) {
    final EqualityGroup group = equalLinks.get(item);
    if (group == null) {
      return true;
    }
    for (final Node node : inequal) {
      if (equalLinks.get(node) == group ||
          item.equals(node)) {
        return false;
      }
    }
    return true;
  }

  public List<Node> reduce() {
    if (!this.checkConsistency()) {
      return Collections.singletonList((Node) NodeValue.newBoolean(false));
    }
    final Set<Node> nodeSet = Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>());
    final List<Node> reduced = new ArrayList<>();

    for (final EqualityGroup group : equalityGroups) {
      if (group.size() > 1) {
        final Node[] nodes = group.toArray();
        nodeSet.addAll(Arrays.asList(nodes));
        reduced.add(new NodeOperation(StandardOperation.EQ, group.toArray()));
      }
    }
    reduced.addAll(filterInequalities(inequalities));
    return reduced;
  }

  private static final class InequalityCache {
    public final Collection<NodeOperation> origin;
    public final List<NodeOperation> filtered;

    public final Map<NodeValue, List<NodeOperation>> constantMap;

    public InequalityCache(Collection<NodeOperation> inequalities) {
      this.origin = inequalities;
      this.filtered = new ArrayList<>();
      this.constantMap = new HashMap<>();

      populate();
    }

    private void populate() {
      for (final NodeOperation ineq : this.origin) {
        int nconst = 0;
        for (int i = 0; i < ineq.getOperandCount(); ++i) {
          final Node node = ineq.getOperand(i);
          if (node.getKind() == Node.Kind.VALUE) {
            putInequality((NodeValue) node, ineq);
            ++nconst;
          }
        }
        if (nconst == 0) {
          filtered.add(ineq);
        }
      }
    }

    private void putInequality(
        final NodeValue node,
        final NodeOperation noteq) {
      if (constantMap.containsKey(node)) {
        constantMap.get(node).add(noteq);
      } else {
        final List<NodeOperation> list = new ArrayList<>();
        list.add(noteq);
        constantMap.put(node, list);
      }
    }
  }

  private Collection<NodeOperation> filterInequalities(
      final Collection<NodeOperation> inequalities) {
    final Set<Node> boundSet = new HashSet<>();
    for (final EqualityGroup group : this.equalityGroups) {
      if (!group.constants.isEmpty()) {
        boundSet.addAll(group.variables);
        boundSet.addAll(group.remains);
      }
    }

    final InequalityCache cache = new InequalityCache(inequalities);
    for (final Map.Entry<NodeValue, List<NodeOperation>> entry : cache.constantMap.entrySet()) {
      final NodeValue value = entry.getKey();
      for (final NodeOperation noteq : entry.getValue()) {
        splitExclude(noteq, value, boundSet, cache.filtered);
      }
    }

    final List<NodeOperation> filtered = cache.filtered;
    for (int i = 0; i < filtered.size(); ++i) {
      final NodeOperation op = filtered.get(i);
      if (ExprUtils.isOperation(op, StandardOperation.NOTEQ)) {
        // inequalities are split pairwise
        filtered.set(i, NOTEQ(op.getOperand(0), op.getOperand(1)));
      }
    }
    return filtered;
  }

  private void splitExclude(
      final NodeOperation noteq,
      final NodeValue constant,
      final Set<Node> boundSet,
      final Collection<NodeOperation> output) {
    final List<Node> operands = new ArrayList<>(noteq.getOperands());
    operands.remove(constant);

    splitNotEqualPairwise(operands, output);
    for (final Node node : operands) {
      if (!boundSet.contains(node)) {
        output.add(NOTEQ(node, constant));
      }
    }
  }

  private static void splitNotEqualPairwise(
      final List<Node> operands,
      final Collection<NodeOperation> output) {
    for (int i = 0; i < operands.size() - 1; ++i) {
      for (int j = i + 1; j < operands.size(); ++j) {
        output.add(NOTEQ(operands.get(i), operands.get(j)));
      }
    }
  }

  private static NodeOperation NOTEQ(final Node lhs, final Node rhs) {
    return Nodes.not(Nodes.eq(lhs, rhs));
  }
}

final class EqualityGroup {
  public final Set<NodeValue> constants;
  public final Set<NodeVariable> variables;
  public final Set<Node> remains;

  public EqualityGroup() {
    this.constants = new HashSet<>();
    this.variables = new HashSet<>();
    this.remains = new HashSet<>();
  }

  public boolean contains(final Node node) {
    switch (node.getKind()) {
    case VARIABLE:
      return variables.contains((NodeVariable) node);

    case VALUE:
      return constants.contains((NodeValue) node);

    default:
      return remains.contains(node);
    }
  }

  public int size() {
    return constants.size() + variables.size() + remains.size();
  }

  public void add(final Node node) {
    switch (node.getKind()) {
    case VARIABLE:
      variables.add((NodeVariable) node);
      break;

    case VALUE:
      constants.add((NodeValue) node);
      break;

    default:
      remains.add(node);
    }
  }

  public void addAll(final Collection<? extends Node> nodes) {
    for (final Node node : nodes) {
      this.add(node);
    }
  }

  public Node[] toArray() {
    final Node[] nodes = new Node[this.size()];
    int i = populate(nodes, 0, variables);
    i = populate(nodes, i, constants);
    populate(nodes, i, remains);

    return nodes;
  }

  private static int populate(
      final Node[] nodes, int i, final Collection<? extends Node> collection) {
    for (final Node node : collection) {
      nodes[i++] = node;
    }
    return i;
  }
}
