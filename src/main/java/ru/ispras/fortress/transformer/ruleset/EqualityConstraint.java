package ru.ispras.fortress.transformer.ruleset;

import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
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

  public void addEquality(Node node) {
    if (!isOperation(node, StandardOperation.EQ)) {
      throw new IllegalArgumentException("EQ operation expected");
    }
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

  private void updateGroupLinks(EqualityGroup group) {
    for (Node node : group.variables) {
      equalLinks.put(node, group);
    }
    for (Node node : group.constants) {
      equalLinks.put(node, group);
    }
    for (Node node : group.remains) {
      equalLinks.put(node, group);
    }
  }

  private EqualityGroup mergeGroupsAdd(Collection<EqualityGroup> groups, Collection<? extends Node> nodes) {
    final EqualityGroup merged = new EqualityGroup();
    for (EqualityGroup group : groups) {
      merged.constants.addAll(group.constants);
    }
    merged.addAll(nodes);
    if (merged.constants.size() > 1) {
      return null;
    }

    for (EqualityGroup group : groups) {
      merged.variables.addAll(group.variables);
      merged.remains.addAll(group.remains);
    }
    return merged;
  }

  public void addInequality(Node node) {
    if (!isOperation(node, StandardOperation.EQ) &&
        !isOperation(node, StandardOperation.NOTEQ)) {
      throw new IllegalArgumentException("EQ or NOTEQ operation expected");
    }
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
    for (NodeOperation noteq : inequalities) {
      collectOperands(operands, noteq);
      for (int i = 0; i < operands.size() - 1; ++i) {
        if (!isNotEqual(operands.get(i), operands.subList(i + 1, operands.size()))) {
          return evaluateTo(false);
        }
      }
      operands.clear();
    }
    return evaluateTo(true);
  }

  private static void collectOperands(List<Node> operands, NodeOperation op) {
    for (int i = 0; i < op.getOperandCount(); ++i) {
      operands.add(op.getOperand(i));
    }
  }

  private static List<Node> collectOperands(NodeOperation op) {
    final List<Node> operands = new ArrayList<>();
    collectOperands(operands, op);
    return operands;
  }

  private boolean isNotEqual(Node item, Collection<? extends Node> inequal) {
    final EqualityGroup group = equalLinks.get(item);
    if (group == null) {
      return true;
    }
    for (Node node : inequal) {
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

    for (EqualityGroup group : equalityGroups) {
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
      for (NodeOperation ineq : this.origin) {
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

    private void putInequality(NodeValue node, NodeOperation noteq) {
      if (constantMap.containsKey(node)) {
        constantMap.get(node).add(noteq);
      } else {
        final List<NodeOperation> list = new ArrayList<>();
        list.add(noteq);
        constantMap.put(node, list);
      }
    }
  }

  private Collection<NodeOperation> filterInequalities(Collection<NodeOperation> inequalities) {
    final Set<Node> boundSet = new HashSet<>();
    for (EqualityGroup group : this.equalityGroups) {
      if (!group.constants.isEmpty()) {
        boundSet.addAll(group.variables);
        boundSet.addAll(group.remains);
      }
    }

    final InequalityCache cache = new InequalityCache(inequalities);
    for (Map.Entry<NodeValue, List<NodeOperation>> entry : cache.constantMap.entrySet()) {
      final NodeValue value = entry.getKey();
      for (NodeOperation noteq : entry.getValue()) {
        splitExclude(noteq, value, boundSet, cache.filtered);
      }
    }

    final List<NodeOperation> filtered = cache.filtered;
    for (int i = 0; i < filtered.size(); ++i) {
      final NodeOperation op = filtered.get(i);
      if (isOperation(op, StandardOperation.EQ)) {
        filtered.set(i, new NodeOperation(StandardOperation.NOT, op));
      }
    }
    return filtered;
  }

  private void splitExclude(NodeOperation noteq, NodeValue constant, Set<Node> boundSet, Collection<NodeOperation> output) {
    final List<Node> operands = collectOperands(noteq);
    operands.remove(constant);

    splitNotEqualPairwise(operands, output);
    for (Node node : operands) {
      if (!boundSet.contains(node)) {
        output.add(NOTEQ(node, constant));
      }
    }
  }

  private static void splitNotEqualPairwise(List<Node> operands, Collection<NodeOperation> output) {
    for (int i = 0; i < operands.size() - 1; ++i) {
      for (int j = i + 1; j < operands.size(); ++j) {
        output.add(NOTEQ(operands.get(i), operands.get(j)));
      }
    }
  }

  private static NodeOperation NOTEQ(Node lhs, Node rhs) {
    return new NodeOperation(StandardOperation.NOT,
                             new NodeOperation(StandardOperation.EQ, lhs, rhs));
  }

  private static boolean isOperation(Node node, Enum<?> opId) {
    notnull(node);
    return node.getKind() == Node.Kind.OPERATION &&
           ((NodeOperation) node).getOperationId() == opId;
  }

  private static void notnull(Object o) {
    if (o == null) {
      throw new NullPointerException();
    }
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

  public boolean contains(Node node) {
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

  public void add(Node node) {
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

  public void addAll(Collection<? extends Node> nodes) {
    for (Node node : nodes) {
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

  private static int populate(Node[] nodes, int i, Collection<? extends Node> collection) {
    for (Node node : collection) {
      nodes[i++] = node;
    }
    return i;
  }
}
