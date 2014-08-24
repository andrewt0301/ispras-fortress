/*
 * Copyright (c) 2013 ISPRAS (www.ispras.ru)
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * Transformer.java, Nov 7, 2013 10:50:53 AM Andrei Tatarnikov
 * 
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not
 * use this file except in compliance with the License. You may obtain a copy of
 * the License at
 * 
 * http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations under
 * the License.
 */

package ru.ispras.fortress.transformer;

import java.util.Map;
import java.util.HashMap;

import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.NodeBinding;

import ru.ispras.fortress.transformer.ruleset.Predicate;

public final class Transformer
{
    private Transformer() {}

    /**
     * Attempts to reduce the specified expression including to a value.
     * Reduction is performed with the help of the calculator object
     * that performs specific operations with specific data types.
     * 
     * The operation may be totally reduced (or, so to speak, reduced to a value),
     * partially reduced or left unchanged. In the last case, the method returns
     * a reference to the current operation (this).
     * 
     * @param options Option flags to tune the reduction strategy.
     * @param expression Expression to be reduced.
     * @return Reduced expression (value or another operation expression
     * with minimal subexpressions) or the initial expression if it is
     * impossible to reduce it.
     * 
     * @throws NullPointerException if any of the parameters is
     * <code>null</code>.
     */

    public static Node reduce(ReduceOptions options, Node expression)
    {
        if (null == options)
            throw new NullPointerException();

        if (null == expression)
            throw new NullPointerException();

        // Only operation expressions can be reduced.
        if (expression.getKind() == Node.Kind.VARIABLE ||
            expression.getKind() == Node.Kind.VALUE)
            return expression;

        if (expression.getKind() == Node.Kind.BINDING)
            return reduceBinding(options, (NodeBinding) expression);

        final OperationReducer reducer = 
            new OperationReducer((NodeOperation) expression, options);

        final Node result = reducer.reduce();
        if (null == result)
            return expression;

        return result;
    }

    private static Node reduceBinding(ReduceOptions options, NodeBinding binding)
    {
        final Node reduced = reduce(options, binding.getExpression());
        if (reduced == null || reduced == binding.getExpression())
            return binding;

        if (reduced.getKind() == Node.Kind.VALUE)
            return reduced;

        return binding.bindTo(reduced);
    }

    /**
     * Substitute given term for variables with specified name in expression.
     * Substitution considers variable names ignoring types.
     *
     * Provided term instance is referenced in resulting expression w/o
     * copying.
     *
     * @param expression Expression in which substitution takes place.
     * @param name Name of variables to be substituted.
     * @param term Term to replace variables.
     * @return An expression where all variables with given name are
     * replaced with term specified.
     *
     * @throws NullPointerException if any of the parameters is
     * <code>null</code>.
     */

    public static Node substitute(Node expression, final String name, final Node term)
    {
        if (expression == null)
            throw new NullPointerException();

        if (name == null)
            throw new NullPointerException();

        if (term == null)
            throw new NullPointerException();

        final TransformerRule rule = new TransformerRule() {
            @Override
            public boolean isApplicable(Node node) {
                return node.getKind() == Node.Kind.VARIABLE
                    && ((NodeVariable) node).getName().equals(name);
            }

            @Override
            public Node apply(Node node) {
                return term;
            }
        };

        final NodeTransformer transformer = new NodeTransformer();
        transformer.addRule(Node.Kind.VARIABLE, rule);
        transformer.walk(expression);
        return transformer.getResult().iterator().next();
    }

    /**
     * Apply given binding substitutions to underlying expression.
     * Substitution applies to single binding provided, ignoring
     * additional bindings in expression. However, nested binding scope is
     * correctly resolved, i.e. substitution applies to free variables
     * in underlying expression and in bound values of nested bindings.
     *
     * @param binding Binding node to be substituted.
     * @return An underlying expression with all bindings specified
     * being substituted.
     *
     * @throws NullPointerException if any of the parameters is
     * <code>null</code>.
     */

    public static Node substituteBinding(NodeBinding binding)
    {
        if (binding == null)
            throw new NullPointerException();

        final Map<String, Node> exprs = new HashMap<String, Node>();
        for (NodeBinding.BoundVariable bound : binding.getBindings())
            exprs.put(bound.getVariable().getName(), bound.getValue());

        final TransformerRule rule = new TransformerRule() {
            @Override
            public boolean isApplicable(Node node) {
                if (node.getKind() != Node.Kind.VARIABLE)
                    return false;

                return exprs.containsKey(((NodeVariable) node).getName());
            }

            @Override
            public Node apply(Node node) {
                return exprs.get(((NodeVariable) node).getName());
            }
        };

        final NodeTransformer transformer = new NodeTransformer();
        transformer.addRule(Node.Kind.VARIABLE, rule);
        transformer.walk(binding.getExpression());

        return transformer.getResult().iterator().next();
    }

    /**
     * Substitute all bindings in given expression.
     * Substitution applies with respect to nested binding scope.
     *
     * Substitution applies non-recursively, i.e. any bindings found
     * in bound values are not substituted.
     *
     * @param expression Expression to be substituted.
     * @return An expression resulting from substitution of all
     * bindings found in initial expression.
     *
     * @throws NullPointerException if any of the parameters is
     * <code>null</code>.
     */

    public static Node substituteAllBindings(Node expression)
    {
        if (expression == null)
            throw new NullPointerException();

        final TransformerRule rule = new TransformerRule() {
            @Override
            public boolean isApplicable(Node node) {
                return node.getKind() == Node.Kind.BINDING;
            }

            @Override
            public Node apply(Node node) {
                return substituteBinding((NodeBinding) node);
            }
        };

        final NodeTransformer transformer = new NodeTransformer();
        transformer.addRule(Node.Kind.BINDING, rule);
        transformer.walk(expression);

        return transformer.getResult().iterator().next();
    }

    /**
     * Transforms given expression according to set of mathematical rules.
     * Transforms composite math predicates such as NEQ, GEQ etc. into formula
     * using NOT, EQ, LE, GE and boolean functions. Works for bitvectors.
     *
     * Transformation considers only standard predicates.
     *
     * @param expression Expression to be transformed.
     * @return An expression resulting from substitution of all
     * bindings found in initial expression.
     *
     * @throws NullPointerException if any of the parameters is
     * <code>null</code>.
     */

    public static Node transformStandardPredicate(Node expression)
    {
        if (expression == null)
            throw new NullPointerException();
        
        final NodeTransformer tl = new NodeTransformer(Predicate.getRuleset());
        tl.walk(expression);
        return tl.getResult().iterator().next();
    }
}
