/*
 * Copyright 2014-2018 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.transformer;

import ru.ispras.fortress.expression.ExprTreeVisitor;
import ru.ispras.fortress.expression.ExprTreeWalker;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeBinding;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.util.InvariantChecks;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;

/**
 * {@link NodeTransformer} is an expression tree visitor with bottom-up substitution policy.
 * Substitutions take place accordingly to set of rules passed to transformer before traversal.
 */
public class NodeTransformer implements ExprTreeVisitor {
  private final Map<Enum<?>, List<TransformerRule>> ruleset;

  private final List<Node[]> operandStack;
  private final List<Node> exprStack;
  private final List<Node> result;
  private final List<NodeBinding.BoundVariable> boundStack;

  /**
   * Traverse and apply substitutions to single expression tree. Resulting expression can be
   * acquired via {@link #getResult()}.
   *
   * @param root Root of a tree to be traversed.
   */
  public void walk(final Node root) {
    final ExprTreeWalker walker = new ExprTreeWalker(this);
    walker.visit(root);
  }

  /**
   * Traverse and apply substitutions to expression forest. Resulting expression can be acquired via
   * {@link #getResult()}.
   *
   * @param trees Collection of root nodes of trees to be traversed.
   */
  public void walk(final Collection<? extends Node> trees) {
    final ExprTreeWalker walker = new ExprTreeWalker(this);
    walker.visit(trees);
  }

  /**
   * Reset transformer to initial state keeping all rules.
   */
  public void reset() {
    this.operandStack.clear();
    this.exprStack.clear();
    this.result.clear();
    this.boundStack.clear();
  }

  /**
   * Create new transformer instance containing no substitution rules.
   */
  public NodeTransformer() {
    this(new IdentityHashMap<Enum<?>, TransformerRule>());
  }

  /**
   * Create new transformer instance with given substitutions rules.
   *
   * @param rules Map of rules. See {@link #addRule addRule()} for details.
   */
  public NodeTransformer(final Map<Enum<?>, TransformerRule> rules) {
    InvariantChecks.checkNotNull(rules);

    ruleset = new IdentityHashMap<>(rules.size());
    for (final Map.Entry<Enum<?>, TransformerRule> entry : rules.entrySet()) {
      addRule(entry.getKey(), entry.getValue());
    }

    operandStack = new ArrayList<>();
    exprStack = new ArrayList<>();
    result = new ArrayList<>();
    boundStack = new ArrayList<>();
  }

  /**
   * Add substitution rule.
   * <p>For rule to be applied to node in expression tree several conditions needs to be hold: 1)
   * either node is NodeOperation with opId operation or node is a Node subclass which kind is opId;
   * 2) rule.isApplicable() should be true for node given.</p>
   *
   * @param opId Target node kind identifier.
   * @param rule Rule to be added.
   *
   * @throws IllegalArgumentException if any of the parameters is {@code null}.
   */
  public void addRule(final Enum<?> opId, final TransformerRule rule) {
    InvariantChecks.checkNotNull(opId);
    InvariantChecks.checkNotNull(rule);

    getRulesWrite(opId).add(rule);
  }

  public void clearRules(final Enum<?> opId) {
    final List<TransformerRule> rules = ruleset.get(opId);
    if (rules != null) {
      rules.clear();
    }
  }

  private List<TransformerRule> getRulesWrite(final Enum<?> opId) {
    List<TransformerRule> rules = ruleset.get(opId);
    if (rules == null) {
      rules = new ArrayList<>();
      ruleset.put(opId, rules);
    }
    return rules;
  }

  private List<TransformerRule> getRulesRead(final Enum<?> opId) {
    final List<TransformerRule> rules = ruleset.get(opId);
    if (rules != null) {
      return rules;
    }
    return Collections.emptyList();
  }

  /**
   * Get collection of expression trees resulting from substitutions done during traversals.
   *
   * @return List of results in order of base forest iteration.
   */
  public List<Node> getResult() {
    return result;
  }

  /**
   * Helper method to conditionally apply rule to node given.
   *
   * @param id Rule search identifier
   * @param node Node to be substituted
   *
   * @return Transformed expression or node itself if no applicable rule can be found.
   */
  private Node applyRule(final Enum<?> id, final Node node) {
    for (final TransformerRule rule : getRulesRead(id)) {
      if (rule.isApplicable(node)) {
        return rule.apply(node);
      }
    }
    return node;
  }

  /**
   * Helper methods to find and apply relevant rule to node given.
   */
  private Node updateNode(final Node node) {
    return applyRule(node.getKind(), node);
  }

  @Override
  public Status getStatus() {
    // We are not going to stop the walker or to skip any subtrees.
    // At least, I (Andrei Tatarnikov) think so.
    // Therefore, it is always OK.

    return Status.OK;
  }

  @Override
  public void onBegin() {}

  @Override
  public void onEnd() {
    assert exprStack.size() == 1;
    result.add(exprStack.remove(0));
  }

  @Override
  public void onOperationBegin(final NodeOperation expr) {
    if (expr.getOperandCount() > 0) {
      operandStack.add(new Node[expr.getOperandCount()]);
    }
  }

  @Override
  public void onOperationEnd(final NodeOperation expr) {
    if (expr.getOperandCount() == 0) {
      exprStack.add(applyRule(expr.getOperationId(), expr));
      return;
    }

    // TODO consecutive rule application
    final int pos = operandStack.size() - 1;
    final Node[] operands = operandStack.remove(pos);
    NodeOperation updated = expr;

    for (int index = 0; index < expr.getOperandCount(); ++index) {
      if (operands[index] != expr.getOperand(index)) {
        updated = new NodeOperation(expr.getOperationId(), operands);
        updated.setUserData(expr.getUserData());
        break;
      }
    }

    Node node = updateNode(updated);
    if (Node.Kind.OPERATION == node.getKind()) {
      node = applyRule(((NodeOperation) node).getOperationId(), node);
    }

    exprStack.add(node);
  }

  @Override
  public int[] getOperandOrder() {
    return null;
  }

  @Override
  public void onOperandBegin(final NodeOperation expr, final Node operand, final int index) {}

  @Override
  public void onOperandEnd(final NodeOperation expr, final Node operand, final int index) {
    Node[] operands = operandStack.get(operandStack.size() - 1);
    operands[index] = exprStack.remove(exprStack.size() - 1);
  }

  @Override
  public void onValue(final NodeValue value) {
    exprStack.add(updateNode(value));
  }

  @Override
  public void onVariable(final NodeVariable variable) {
    exprStack.add(updateNode(variable));
  }

  @Override
  public void onBindingBegin(final NodeBinding node) {}

  @Override
  public void onBindingListEnd(final NodeBinding node) {
    final int fromIndex = boundStack.size() - node.getBindings().size();

    final List<NodeBinding.BoundVariable> bindings =
        boundStack.subList(fromIndex, boundStack.size());

    final NodeBinding updated = new NodeBinding(node.getExpression(), bindings);
    updated.setUserData(node.getUserData());

    final TransformerRule scopedRule =
        new RejectBoundVariablesRule(getRulesWrite(Node.Kind.VARIABLE), updated);

    // box scoped rule
    ruleset.put(Node.Kind.VARIABLE, Collections.singletonList(scopedRule));
    bindings.clear();
  }

  @Override
  public void onBindingEnd(final NodeBinding node) {
    // unbox scoped rule
    final RejectBoundVariablesRule rule =
        (RejectBoundVariablesRule) ruleset.get(Node.Kind.VARIABLE).get(0);
    ruleset.put(Node.Kind.VARIABLE, rule.getShadowedRules());

    final Node expr = exprStack.remove(exprStack.size() - 1);
    final NodeBinding bindingNode = rule.getBinding().bindTo(expr);
    exprStack.add(updateNode(bindingNode));
  }

  @Override
  public void onBoundVariableBegin(
      final NodeBinding node,
      final NodeVariable variable,
      final Node value) {}

  @Override
  public void onBoundVariableEnd(
      final NodeBinding node,
      final NodeVariable variable,
      final Node value) {
    final Node updatedValue = exprStack.remove(exprStack.size() - 1);
    boundStack.add(NodeBinding.bindVariable(variable, updatedValue));
  }

  /**
   * ScopedBindingRule is base class for rules respecting variable binding visibility scope.
   * <p>Implementors are organized in nesting scopes list with inner scope being responsible for
   * passing request to outer scope if it cannot be satisfied by himself.
   * Subclasses are expected to implement TransformRule.isApplicable() method that should set
   * applicableCache member to correct substitution result in case rule is applicable.</p>
   */
  private abstract static class ScopedBindingRule implements TransformerRule {
    protected final List<TransformerRule> shadowed;
    protected final Map<String, Node> bindings;
    protected Node applicableCache;

    /**
     * Create rule for nested variable scope.
     *
     * @param previous Rule representing outer scope.
     * @param bindingList List of bound variables in current scope.
     */
    public ScopedBindingRule(
        final List<TransformerRule> previous,
        final List<NodeBinding.BoundVariable> bindingList) {
      this.shadowed = previous;
      this.bindings = new HashMap<>();
      for (final NodeBinding.BoundVariable bound : bindingList) {
        bindings.put(bound.getVariable().getName(), bound.getValue());
      }
      this.applicableCache = null;
    }

    @Override
    public Node apply(final Node node) {
      return applicableCache;
    }

    /**
     * Get rule being shadowed by current scope.
     */
    public List<TransformerRule> getShadowedRules() {
      return shadowed;
    }
  }


  /**
   * RejectBoundVariablesRule works as a filter ignoring any variable nodes considered bound in
   * current nested variable scope.
   * <p>As described in {@link ScopedBindingRule}, rules are organized in nesting variable scopes
   * list. Therefore first ignoring any variable bound in current scope or delegating check to outer
   * scope otherwise brings requierd result.</p>
   */
  private static final class RejectBoundVariablesRule extends ScopedBindingRule {
    private final NodeBinding node;

    /**
     * Create filter wrapper for existing rule.
     *
     * @param previous Rule representing outer scope.
     * @param node NodeBinding instance is to check for.
     */
    public RejectBoundVariablesRule(final List<TransformerRule> previous, final NodeBinding node) {
      super(previous, node.getBindings());
      this.node = node;
    }

    /**
     * Get binding being ignored by this rule.
     */
    public NodeBinding getBinding() {
      return node;
    }

    @Override
    public boolean isApplicable(final Node node) {
      if (node.getKind() != Node.Kind.VARIABLE) {
        return false;
      }

      final NodeVariable variable = (NodeVariable) node;

      // variable is bound
      if (bindings.containsKey(variable.getName())) {
        return false;
      }

      for (final TransformerRule rule : getShadowedRules()) {
        if (rule.isApplicable(node)) {
          applicableCache = rule.apply(node);
          return true;
        }
      }
      return false;
    }
  }
}
