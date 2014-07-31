/*
 * Copyright (c) 2013 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * Transformer.java, Nov 7, 2013 10:50:53 AM Andrei Tatarnikov
 */

package ru.ispras.fortress.transformer;

import java.util.Map;
import java.util.HashMap;

import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeExpr;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.NodeBinding;

import ru.ispras.fortress.transformer.ruleset.Predicate;

public final class Transformer
{
    /**
     * Attempts to reduce the operation expression including all of its child
     * operations to a value. Reduction is performed with the help of the calculator
     * object that performs specific operations with specific data types.
     * 
     * The operation may be totally reduced (or, so to speak, reduced to a value),
     * partially reduced or left unchanged. In the last case, the method returns
     * a reference to the current operation (this).
     * 
     * @param options Option flags to tune the reduction strategy.
     * @param expression Expression to be reduced.
     * @return An element that describes the reduced operation expression
     * (a value or another operation expression with minimal subexpressions) or
     * this if it is impossible to reduce the operation expression.
     */

    public static Node reduce(ReduceOptions options, NodeExpr expression)
    {
        final OperationReducer reducer = new OperationReducer(expression, options);
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

        final LocalTransformer transformer = new LocalTransformer();
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

        final LocalTransformer transformer = new LocalTransformer();
        transformer.addRule(Node.Kind.VARIABLE, rule);
        transformer.walk(node);

        final NodeBinding out =
            (NodeBinding) transformer.getResult().iterator().next();

        return out.getExpression();
    }

    public static Node transformStandardPredicate(Node expr)
    {
        if (expr == null)
            throw new NullPointerException();
        
        final LocalTransformer tl = new LocalTransformer(Predicate.getRuleset());
        tl.walk(expr);
        return tl.getResult().iterator().next();
    }
}
