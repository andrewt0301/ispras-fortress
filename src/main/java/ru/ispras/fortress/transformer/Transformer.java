/*
 * Copyright 2013-2018 ISP RAS (http://www.ispras.ru)
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

import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.ExprUtils;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeBinding;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.transformer.ruleset.Predicate;
import ru.ispras.fortress.util.InvariantChecks;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * The {@link Transformer} class contains static methods for common expression transformations.
 */
public final class Transformer {
  private Transformer() {}

  /**
   * Substitute given term for variables with specified name in expression. Substitution considers
   * variable names ignoring types.
   * <p>Provided term instance is referenced in resulting expression w/o copying.</p>
   *
   * @param expression Expression in which substitution takes place.
   * @param name Name of variables to be substituted.
   * @param term Term to replace variables.
   * @return An expression where all variables with given name are replaced with term specified.
   *
   * @throws IllegalArgumentException if any of the parameters is {@code null}.
   */
  public static Node substitute(final Node expression, final String name, final Node term) {
    InvariantChecks.checkNotNull(expression);
    InvariantChecks.checkNotNull(name);
    InvariantChecks.checkNotNull(term);

    final TransformerRule rule = new TransformerRule() {
      @Override
      public boolean isApplicable(final Node node) {
        return ExprUtils.isVariable(node) && ((NodeVariable) node).getName().equals(name);
      }

      @Override
      public Node apply(final Node node) {
        return term;
      }
    };

    return transform(expression, Node.Kind.VARIABLE, rule);
  }

  public static Node substitute(final Node expression, final VariableProvider variableProvider) {
    InvariantChecks.checkNotNull(expression);
    InvariantChecks.checkNotNull(variableProvider);

    final TransformerRule rule = new TransformerRule() {
      @Override
      public boolean isApplicable(final Node node) {
        return ExprUtils.isVariable(node);
      }

      @Override
      public Node apply(final Node node) {
        final Variable prev = ((NodeVariable) node).getVariable();
        final Variable next = variableProvider.getVariable(prev);
        if (next != null) {
          return new NodeVariable(next);
        }
        return node;
      }
    };

    return transform(expression, Node.Kind.VARIABLE, rule);
  }

  /**
   * Apply given binding substitutions to underlying expression. Substitution applies to single
   * binding provided, ignoring additional bindings in expression. However, nested binding scope is
   * correctly resolved, i.e. substitution applies to free variables in underlying expression and in
   * bound values of nested bindings.
   *
   * @param binding Binding node to be substituted.
   * @return An underlying expression with all bindings specified being substituted.
   *
   * @throws IllegalArgumentException if any of the parameters is {@code null}.
   */
  public static Node substituteBinding(final NodeBinding binding) {
    InvariantChecks.checkNotNull(binding);

    final Map<String, Node> exprs = new HashMap<>();
    for (final NodeBinding.BoundVariable bound : binding.getBindings()) {
      exprs.put(bound.getVariable().getName(), bound.getValue());
    }

    final TransformerRule rule = new TransformerRule() {
      @Override
      public boolean isApplicable(final Node node) {
        return ExprUtils.isVariable(node) && exprs.containsKey(((NodeVariable) node).getName());
      }

      @Override
      public Node apply(final Node node) {
        return exprs.get(((NodeVariable) node).getName());
      }
    };

    return transform(binding.getExpression(), Node.Kind.VARIABLE, rule);
  }

  /**
   * Substitute all bindings in given expression. Substitution applies with respect to nested
   * binding scope.
   * <p>Substitution applies non-recursively, i.e. any bindings found in bound values are not
   * substituted.</p>
   *
   * @param expression Expression to be substituted.
   * @return An expression resulting from substitution of all bindings found in initial expression.
   *
   * @throws IllegalArgumentException if any of the parameters is {@code null}.
   */
  public static Node substituteAllBindings(final Node expression) {
    InvariantChecks.checkNotNull(expression);

    final TransformerRule rule = new TransformerRule() {
      @Override
      public boolean isApplicable(final Node node) {
        return ExprUtils.isBinding(node);
      }

      @Override
      public Node apply(final Node node) {
        return substituteBinding((NodeBinding) node);
      }
    };

    return transform(expression, Node.Kind.BINDING, rule);
  }

  /**
   * Replace operations in expression with standard counterparts. Transforms composite math
   * predicates such as NEQ, GEQ etc. into formula using NOT, EQ, LE, GE and boolean functions.
   * Supports general and bitvector operations.
   * <p>Transformation considers only standard predicates.</p>
   *
   * @param expression Expression to be transformed.
   * @return Expression with non-standard operations being replaced.
   *
   * @throws IllegalArgumentException if any of the parameters is {@code null}.
   */
  public static Node standardize(final Node expression) {
    InvariantChecks.checkNotNull(expression);

    // Reduce expression before standardizing.
    final Node reducedExpression = Reducer.reduce(ReduceOptions.NEW_INSTANCE, expression);

    final NodeTransformer transformer = new NodeTransformer(Predicate.getStandardRuleset());
    return transform(reducedExpression, transformer);
  }

  /**
   * Transforms an expression using the given rule.
   *
   * @param tree Expression to be transformed.
   * @param indicator Node kind or operation id of nodes rule is to be applied to.
   * @param rule Transformation rule.
   *
   * @return Transformed expression.
   *
   * @throws IllegalArgumentException if any of the parameters is {@code null}.
   */
  public static Node transform(
      final Node tree,
      final Enum<?> indicator,
      final TransformerRule rule) {
    return transform(tree, newNodeTransformer(indicator, rule));
  }

  /**
   * Transforms an expression using the given transformer.
   *
   * @param tree Expression to be transformed.
   * @param transformer Transformer for be used.
   *
   * @return Transformed expression.
   *
   * @throws IllegalArgumentException if any of the parameters is {@code null}.
   */
  public static Node transform(final Node tree, final NodeTransformer transformer) {
    InvariantChecks.checkNotNull(tree);
    InvariantChecks.checkNotNull(transformer);

    transformer.walk(tree);

    final Node result = transformer.getResult().iterator().next();
    transformer.reset();

    return result;
  }

  /**
   * Transforms a collection of expressions using the given rule.
   *
   * @param forest Collection of expressions to be transformed.
   * @param indicator Node kind or operation id of nodes rule is to be applied to.
   * @param rule Transformation rule.
   *
   * @return List of transformed expressions in order of base collection iteration.
   *
   * @throws IllegalArgumentException if any of the parameters is {@code null}.
   */
  public static List<Node> transformAll(
      final Collection<? extends Node> forest,
      final Enum<?> indicator,
      final TransformerRule rule) {
    return transformAll(forest, newNodeTransformer(indicator, rule));
  }

  /**
   * Transforms a collection of expressions using the given rule.
   *
   * @param forest Collection of expressions to be transformed.
   * @param transformer Transformer for be used.
   *
   * @return List of transformed expressions in order of base collection iteration.
   *
   * @throws IllegalArgumentException if any of the parameters is {@code null}.
   */
  public static List<Node> transformAll(
      final Collection<? extends Node> forest,
      final NodeTransformer transformer) {
    InvariantChecks.checkNotNull(forest);
    InvariantChecks.checkNotNull(transformer);

    transformer.walk(forest);

    final List<Node> result = new ArrayList<>(transformer.getResult());
    transformer.reset();

    return result;
  }

  /**
   * Constructs a node transformer for the given transformation rule.
   *
   * @param indicator Node kind or operation id of nodes rule is to be applied to.
   * @param rule Transformation rule.
   *
   * @return Node transformer for the given transformation rule.
   *
   * @throws IllegalArgumentException if any of the parameters is {@code null}.
   */
  private static NodeTransformer newNodeTransformer(
      final Enum<?> indicator,
      final TransformerRule rule) {
    InvariantChecks.checkNotNull(indicator);
    InvariantChecks.checkNotNull(rule);

    final NodeTransformer transformer = new NodeTransformer();
    transformer.addRule(indicator, rule);

    return transformer;
  }
}
