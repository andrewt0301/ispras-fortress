/*
 * Copyright 2013-2017 ISP RAS (http://www.ispras.ru)
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

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import ru.ispras.fortress.calculator.CalculatorEngine;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeBinding;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.transformer.ruleset.Predicate;
import ru.ispras.fortress.util.InvariantChecks;

/**
 * The {@link Transformer} class contains static methods for common expression transformations.
 */
public final class Transformer {
  private Transformer() {}

  /**
   * Attempts to reduce the specified expression including to a value. Reduction is performed with
   * the help of the calculator object that performs specific operations with specific data types.
   *
   * The operation may be totally reduced (or, so to speak, reduced to a value), partially reduced
   * or left unchanged. In the last case, the method returns a reference to the current operation
   * (this).
   *
   * @param engine Calculator engine (if {@code null}, the default engine to be used).
   * @param options Option flags to tune the reduction strategy.
   * @param expression Expression to be reduced.
   * @return Reduced expression (value or another operation expression with minimal subexpressions)
   *         or the initial expression if it is impossible to reduce it.
   *
   * @throws IllegalArgumentException if any of the parameters is {@code null}.
   */
  public static Node reduce(
      final CalculatorEngine engine,
      final ReduceOptions options,
      final Node expression) {
    InvariantChecks.checkNotNull(options);
    InvariantChecks.checkNotNull(expression);

    // Only operation expressions can be reduced.
    if (expression.getKind() == Node.Kind.VARIABLE ||
        expression.getKind() == Node.Kind.VALUE) {
      return expression;
    }

    if (expression.getKind() == Node.Kind.BINDING) {
      return reduceBinding(engine, options, (NodeBinding) expression);
    }

    final OperationReducer reducer =
        new OperationReducer(engine, (NodeOperation) expression, options);

    final Node result = reducer.reduce();
    if (null == result) {
      return expression;
    }

    return result;
  }

  /**
   * Attempts to reduce the specified expression including to a value.
   * Uses default {@code engine}.
   *
   * @see Transformer#reduce(CalculatorEngine, ReduceOptions, Node)
   */
  public static Node reduce(final ReduceOptions options, final Node expression) {
    return reduce(null, options, expression);
  }

  /**
   * Attempts to reduce the specified expression including to a value.
   * Uses default {@code engine} with {@link ReduceOptions#NEW_INSTANCE} policy.
   *
   * @see Transformer#reduce(CalculatorEngine, ReduceOptions, Node)
   */
  public static Node reduce(final Node e) {
    return reduce(null, ReduceOptions.NEW_INSTANCE, e);
  }

  private static Node reduceBinding(
      final CalculatorEngine engine,
      final ReduceOptions options,
      final NodeBinding binding) {
    final Node reduced = reduce(engine, options, binding.getExpression());
    if (reduced == null || reduced == binding.getExpression()) {
      return binding;
    }

    if (reduced.getKind() == Node.Kind.VALUE) {
      return reduced;
    }

    return binding.bindTo(reduced);
  }

  /**
   * Substitute given term for variables with specified name in expression. Substitution considers
   * variable names ignoring types.
   *
   * Provided term instance is referenced in resulting expression w/o copying.
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
        return node.getKind() == Node.Kind.VARIABLE && ((NodeVariable) node).getName().equals(name);
      }

      @Override
      public Node apply(final Node node) {
        return term;
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
        return node.getKind() == Node.Kind.VARIABLE
            && exprs.containsKey(((NodeVariable) node).getName());
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
   *
   * Substitution applies non-recursively, i.e. any bindings found in bound values are not
   * substituted.
   *
   * @param expression Expression to be substituted.
   * @return An expression resulting from substitution of all bindings found in initial expression.
   *
   * @throws IllegalArgumentException if any of the parameters is <code>null</code>.
   */
  public static Node substituteAllBindings(final Node expression) {
    InvariantChecks.checkNotNull(expression);

    final TransformerRule rule = new TransformerRule() {
      @Override
      public boolean isApplicable(final Node node) {
        return node.getKind() == Node.Kind.BINDING;
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
   *
   * Transformation considers only standard predicates.
   *
   * @param expression Expression to be transformed.
   * @return Expression with non-standard operations being replaced.
   *
   * @throws IllegalArgumentException if any of the parameters is {@code null}.
   */
  public static Node standardize(final Node expression) {
    InvariantChecks.checkNotNull(expression);

    /* Reduce expression before standardizing. */
    final Node reducedExpression = Transformer.reduce(ReduceOptions.NEW_INSTANCE, expression);

    final NodeTransformer tl = new NodeTransformer(Predicate.getStandardRuleset());
    tl.walk(reducedExpression);
    return tl.getResult().iterator().next();
  }

  /**
   * Transform expression using given rule.
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
    InvariantChecks.checkNotNull(tree);
    return transformAll(Collections.singleton(tree), indicator, rule).get(0);
  }

  /**
   * Transform collection of expressions using given rule.
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
      final Collection<Node> forest,
      final Enum<?> indicator,
      final TransformerRule rule) {
    InvariantChecks.checkNotNull(forest);
    InvariantChecks.checkNotNull(indicator);
    InvariantChecks.checkNotNull(rule);

    final NodeTransformer transformer = new NodeTransformer();
    transformer.addRule(indicator, rule);
    transformer.walk(forest);

    return transformer.getResult();
  }
}
