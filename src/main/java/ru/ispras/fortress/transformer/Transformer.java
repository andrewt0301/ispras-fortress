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
        if (expression.getKind() != Node.Kind.OPERATION)
            return expression;

        final OperationReducer reducer = 
            new OperationReducer((NodeOperation) expression, options);

        final Node result = reducer.reduce();
        if (null == result)
            return expression;

        return result;
    }

    public static Node substitute(Node expr, final String name, final Node term)
    {
        if (expr == null || name == null || term == null)
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
        transformer.walk(expr);
        return transformer.getResult().iterator().next();
    }

    public static Node substituteBinding(NodeBinding node)
    {
        if (node == null)
            throw new NullPointerException();

        final Map<String, Node> exprs = new HashMap<String, Node>();
        for (NodeBinding.BoundVariable bound : node.getBindings())
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
        transformer.walk(node.getExpression());

        return transformer.getResult().iterator().next();
    }

    public static Node substituteAllBindings(Node node)
    {
        if (node == null)
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
        transformer.walk(node);

        return transformer.getResult().iterator().next();
    }

    public static Node transformStandardPredicate(Node expr)
    {
        if (expr == null)
            throw new NullPointerException();
        
        final NodeTransformer tl = new NodeTransformer(Predicate.getRuleset());
        tl.walk(expr);
        return tl.getResult().iterator().next();
    }
}
