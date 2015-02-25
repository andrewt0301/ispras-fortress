/*
 * Copyright 2014 ISP RAS (http://www.ispras.ru)
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

import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.HashMap;
import java.util.IdentityHashMap;

import ru.ispras.fortress.expression.*;

/**
 * NodeTransformer is an experssion tree visitor with bottom-up substitution policy. Substitutions
 * take place accordingly to set of rules passed to transformer before traversal.
 */

public class NodeTransformer implements ExprTreeVisitor {
  // TODO use list of rules for enum as priority queue
  private final Map<Enum<?>, TransformerRule> ruleset;

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

  public void walk(Node root) {
    final ExprTreeWalker walker = new ExprTreeWalker(this);
    walker.visit(root);
  }

  /**
   * Traverse and apply substitutions to expression forest. Resulting expression can be acquired via
   * {@link #getResult()}.
   * 
   * @param trees Collections of root nodes of trees to be traversed.
   */

  public void walk(Iterable<? extends Node> trees) {
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

  public NodeTransformer(Map<Enum<?>, TransformerRule> rules) {
    if (rules == null) {
      throw new NullPointerException();
    }

    ruleset = new IdentityHashMap<>(rules);
    operandStack = new ArrayList<>();
    exprStack = new ArrayList<>();
    result = new ArrayList<>();
    boundStack = new ArrayList<>();
  }

  /**
   * Add substitution rule.
   * 
   * For rule to be applied to node in expression tree several conditions needs to be hold: 1)
   * either node is NodeOperation with opId operation or node is a Node subclass which kind is opId;
   * 2) rule.isApplicable() should be true for node given.
   * 
   * @param opId Target node kind identifier.
   * @param rule Rule to be added.
   */

  public void addRule(Enum<?> opId, TransformerRule rule) {
    if (opId == null || rule == null) {
      throw new NullPointerException();
    }

    // TODO check for replacements or/and add to end of queue
    ruleset.put(opId, rule);
  }

  /**
   * Get collection of expression trees resulting from substitutions done during traversals.
   */

  public Iterable<Node> getResult() {
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

  private Node applyRule(Enum<?> id, Node node) {
    final TransformerRule rule = ruleset.get(id);
    if (rule != null && rule.isApplicable(node)) {
      return rule.apply(node);
    }
    return node;
  }

  /**
   * Helper methods to find and apply relevant rule to node given.
   */

  private Node updateNode(Node node) {
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
  public void onRootBegin() {}

  @Override
  public void onRootEnd() {
    assert exprStack.size() == 1;
    result.add(exprStack.remove(0));
  }

  @Override
  public void onOperationBegin(NodeOperation expr) {
    if (expr.getOperandCount() > 0) {
      operandStack.add(new Node[expr.getOperandCount()]);
    }
  }

  @Override
  public void onOperationEnd(NodeOperation expr) {
    if (expr.getOperandCount() == 0) {
      exprStack.add(applyRule(expr.getOperationId(), expr));
      return;
    }

    final int pos = operandStack.size() - 1;
    final Enum<?> opId = expr.getOperationId();

    // TODO consequtive rule application
    Node node = applyRule(opId, new NodeOperation(opId, operandStack.remove(pos)));
    exprStack.add(node);
  }

  @Override
  public int[] getOperandOrder() {
    return null;
  }

  @Override
  public void onOperandBegin(NodeOperation expr, Node operand, int index) {}

  @Override
  public void onOperandEnd(NodeOperation expr, Node operand, int index) {
    Node[] operands = operandStack.get(operandStack.size() - 1);
    operands[index] = exprStack.remove(exprStack.size() - 1);
  }

  @Override
  public void onValue(NodeValue value) {
    exprStack.add(updateNode(value));
  }

  @Override
  public void onVariable(NodeVariable variable) {
    exprStack.add(updateNode(variable));
  }

  @Override
  public void onBindingBegin(NodeBinding node) {}

  @Override
  public void onBindingListEnd(NodeBinding node) {
    final int fromIndex = boundStack.size() - node.getBindings().size();

    final List<NodeBinding.BoundVariable> bindings =
        boundStack.subList(fromIndex, boundStack.size());

    final TransformerRule scopedRule =
        new RejectBoundVariablesRule(ruleset.get(Node.Kind.VARIABLE), new NodeBinding(
            node.getExpression(), bindings));

    ruleset.put(Node.Kind.VARIABLE, scopedRule);
    bindings.clear();
  }

  @Override
  public void onBindingEnd(NodeBinding node) {
    final RejectBoundVariablesRule rule =
        (RejectBoundVariablesRule) ruleset.get(Node.Kind.VARIABLE);
    ruleset.put(Node.Kind.VARIABLE, rule.getShadowedRule());

    final Node expr = exprStack.remove(exprStack.size() - 1);
    final NodeBinding bindingNode = rule.getBinding().bindTo(expr);
    exprStack.add(updateNode(bindingNode));
  }

  @Override
  public void onBoundVariableBegin(NodeBinding node, NodeVariable variable, Node value) {}

  @Override
  public void onBoundVariableEnd(NodeBinding node, NodeVariable variable, Node value) {
    final Node updatedValue = exprStack.remove(exprStack.size() - 1);
    boundStack.add(NodeBinding.bindVariable(variable, updatedValue));
  }
}


/**
 * ScopedBindingRule is base class for rules respecting variable binding visibility scope.
 * 
 * Implementors are organized in nesting scopes list with inner scope being responsible for passing
 * request to outer scope if it cannot be satisfied by himself.
 * 
 * Subclasses are expected to implement TransformRule.isApplicable() method that should set
 * applicableCache member to correct substitution result in case rule is applicable.
 */

abstract class ScopedBindingRule implements TransformerRule {
  protected final TransformerRule shadowed;
  protected final Map<String, Node> bindings;
  protected Node applicableCache;

  /**
   * Create rule for nested variable scope.
   * 
   * @param previous Rule representing outer scope.
   * @param bindingList List of bound variables in current scope.
   */

  public ScopedBindingRule(TransformerRule previous, List<NodeBinding.BoundVariable> bindingList) {
    this.shadowed = previous;
    this.bindings = new HashMap<>();
    for (NodeBinding.BoundVariable bound : bindingList) {
      bindings.put(bound.getVariable().getName(), bound.getValue());
    }
    this.applicableCache = null;
  }

  @Override
  public Node apply(Node node) {
    return applicableCache;
  }

  /**
   * Get rule being shadowed by current scope.
   */

  public TransformerRule getShadowedRule() {
    return shadowed;
  }
}


/**
 * RejectBoundVariablesRule works as a filter ignoring any variable nodes considered bound in
 * current nested variable scope.
 * 
 * As described in {@link ScopedBindingRule}, rules are organized in nesting variable scopes list.
 * Therefore first ignoring any variable bound in current scope or delegating check to outer scope
 * otherwise brings requierd result.
 */

final class RejectBoundVariablesRule extends ScopedBindingRule {
  private final NodeBinding node;

  /**
   * Create filter wrapper for existing rule.
   * 
   * @param previous Rule representing outer scope.
   * @param node NodeBinding instance is to check for.
   */

  public RejectBoundVariablesRule(TransformerRule previous, NodeBinding node) {
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
  public boolean isApplicable(Node node) {
    if (node.getKind() != Node.Kind.VARIABLE) {
      return false;
    }

    final NodeVariable variable = (NodeVariable) node;

    // variable is bound
    if (bindings.containsKey(variable.getName())) {
      return false;
    }

    if (shadowed == null) {
      return false;
    }

    boolean applicable = shadowed.isApplicable(node);
    if (applicable) {
      applicableCache = shadowed.apply(node);
    }
    return applicable;
  }
}
