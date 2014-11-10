/*
 * Copyright 2014 ISP RAS (http://www.ispras.ru)
 * 
 * Licensed under the Apache License, Version 2.0 (the "License"); you may
 * not use this file except in compliance with the License. You may obtain
 * a copy of the License at
 * 
 * http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package ru.ispras.fortress.transformer.ruleset;

import java.util.Map;
import java.util.IdentityHashMap;

import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.transformer.TransformerRule;

/**
 *  ExpressionRule is a base class for rules applicable to single
 *  operation type.
 */

abstract class ExpressionRule implements TransformerRule
{
    private Enum<?> opId;

    /**
     *  Create new rule for given operation.
     *
     *  @param opId Operation identifier for this rule.
     */

    public ExpressionRule(Enum<?> opId)
    {
        if (opId == null)
            throw new NullPointerException();

        this.opId = opId;
    }

    /**
     *  Get operation identifier for this rule.
     */

    public Enum<?> getOperationId()
    {
        return opId;
    }

    @Override
    public boolean isApplicable(Node node)
    {
        return node.getKind() == Node.Kind.OPERATION
            && ((NodeOperation) node).getOperationId() == opId;
    }

    public abstract Node apply(Node node);

    /**
     *  Helper method to extract operands from node.
     *
     *  @param node Operation node to extract operands from.
     */

    protected static Node[] extractOperands(Node node)
    {
        NodeOperation in = (NodeOperation) node;
        Node[] operands = new Node[in.getOperandCount()];
        for (int i = 0; i < operands.length; ++i)
            operands[i] = in.getOperand(i);

        return operands;
    }
}

public final class Predicate
{
    /**
     *  Create ruleset for standard predicate transformations.
     */

    public static Map<Enum<?>, TransformerRule> getRuleset()
    {
        Map<Enum<?>, TransformerRule> ruleset =
            new IdentityHashMap<Enum<?>, TransformerRule>();

        ExpressionRule rule;

        rule = new ExpressionRule(StandardOperation.NOTEQ) {
            @Override
            public Node apply(Node in) {
                return new NodeOperation(
                    StandardOperation.NOT,
                    new NodeOperation(StandardOperation.EQ, extractOperands(in)));
            }
        };
        ruleset.put(rule.getOperationId(), rule);
   
        rule = new ExpressionRule(StandardOperation.LESSEQ) {
            @Override
            public Node apply(Node in) {
                Node[] operands = extractOperands(in);
                return new NodeOperation(
                    StandardOperation.OR,
                    new NodeOperation(StandardOperation.LESS, operands),
                    new NodeOperation(StandardOperation.EQ, operands));
            }
        };
        ruleset.put(rule.getOperationId(), rule);
   
        rule = new ExpressionRule(StandardOperation.GREATER) {
            @Override
            public Node apply(Node in) {
                Node [] operands = extractOperands(in);
                return new NodeOperation(
                    StandardOperation.AND,
                    new NodeOperation(StandardOperation.NOT,
                        new NodeOperation(StandardOperation.LESS, operands)),
                    new NodeOperation(StandardOperation.NOT,
                        new NodeOperation(StandardOperation.EQ, operands)));
            }
        };
        ruleset.put(rule.getOperationId(), rule);
   
        rule = new ExpressionRule(StandardOperation.GREATEREQ) {
            @Override
            public Node apply(Node in) {
                return new NodeOperation(
                    StandardOperation.NOT,
                    new NodeOperation(StandardOperation.LESS, extractOperands(in)));
            }
        };
        ruleset.put(rule.getOperationId(), rule);

        rule = new ExpressionRule(StandardOperation.BVULE) {
            @Override
            public Node apply(Node in) {
                Node[] operands = extractOperands(in);
                return new NodeOperation(
                    StandardOperation.OR,
                    new NodeOperation(StandardOperation.BVULT, operands),
                    new NodeOperation(StandardOperation.EQ, operands));
            }
        };
        ruleset.put(rule.getOperationId(), rule);

        rule = new ExpressionRule(StandardOperation.BVUGE) {
            @Override
            public Node apply(Node in) {
                return new NodeOperation(
                    StandardOperation.NOT,
                    new NodeOperation(StandardOperation.BVULT, extractOperands(in)));
            }
        };
        ruleset.put(rule.getOperationId(), rule);

        rule = new ExpressionRule(StandardOperation.BVUGT) {
            @Override
            public Node apply(Node in) {
                Node [] operands = extractOperands(in);
                return new NodeOperation(
                    StandardOperation.AND,
                    new NodeOperation(StandardOperation.NOT,
                        new NodeOperation(StandardOperation.BVULT, operands)),
                    new NodeOperation(StandardOperation.NOT,
                        new NodeOperation(StandardOperation.EQ, operands)));
            }
        };
        ruleset.put(rule.getOperationId(), rule);

        rule = new ExpressionRule(StandardOperation.BVSLE) {
            @Override
            public Node apply(Node in) {
                Node[] operands = extractOperands(in);
                return new NodeOperation(
                    StandardOperation.OR,
                    new NodeOperation(StandardOperation.BVSLT, operands),
                    new NodeOperation(StandardOperation.EQ, operands));
            }
        };
        ruleset.put(rule.getOperationId(), rule);

        rule = new ExpressionRule(StandardOperation.BVSGE) {
            @Override
            public Node apply(Node in) {
                return new NodeOperation(
                    StandardOperation.NOT,
                    new NodeOperation(StandardOperation.BVSLT, extractOperands(in)));
            }
        };
        ruleset.put(rule.getOperationId(), rule);

        rule = new ExpressionRule(StandardOperation.BVSGT) {
            @Override
            public Node apply(Node in) {
                Node [] operands = extractOperands(in);
                return new NodeOperation(
                    StandardOperation.AND,
                    new NodeOperation(StandardOperation.NOT,
                        new NodeOperation(StandardOperation.BVSLT, operands)),
                    new NodeOperation(StandardOperation.NOT,
                        new NodeOperation(StandardOperation.EQ, operands)));
            }
        };
        ruleset.put(rule.getOperationId(), rule);
        return ruleset;
    }
}
