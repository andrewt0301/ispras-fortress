package ru.ispras.fortress.transformer.ruleset;

import java.util.Map;
import java.util.IdentityHashMap;

import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeExpr;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.transformer.TransformerRule;

abstract class ExpressionRule implements TransformerRule
{
    private Enum<?> opId;

    public ExpressionRule(Enum<?> opId)
    {
        if (opId == null)
            throw new NullPointerException();

        this.opId = opId;
    }

    public Enum<?> getOperationId()
    {
        return opId;
    }

    public boolean isApplicable(Node node)
    {
        return node.getKind() == Node.Kind.EXPR
            && ((NodeExpr) node).getOperationId() == opId;
    }

    public abstract Node apply(Node node);

    protected static Node[] extractOperands(Node node)
    {
        NodeExpr in = (NodeExpr) node;
        Node[] operands = new Node[in.getOperandCount()];
        for (int i = 0; i < operands.length; ++i)
            operands[i] = in.getOperand(i);

        return operands;
    }
}

public final class Predicate
{
    public static Map<Enum<?>, TransformerRule> getRuleset()
    {
        Map<Enum<?>, TransformerRule> ruleset =
            new IdentityHashMap<Enum<?>, TransformerRule>();

        ExpressionRule rule;

        rule = new ExpressionRule(StandardOperation.NOTEQ) {
            @Override
            public Node apply(Node in) {
                return new NodeExpr(
                    StandardOperation.NOT,
                    new NodeExpr(StandardOperation.EQ, extractOperands(in)));
            }
        };
        ruleset.put(rule.getOperationId(), rule);
   
        rule = new ExpressionRule(StandardOperation.LESSEQ) {
            @Override
            public Node apply(Node in) {
                Node[] operands = extractOperands(in);
                return new NodeExpr(
                    StandardOperation.OR,
                    new NodeExpr(StandardOperation.LESS, operands),
                    new NodeExpr(StandardOperation.EQ, operands));
            }
        };
        ruleset.put(rule.getOperationId(), rule);
   
        rule = new ExpressionRule(StandardOperation.GREATER) {
            @Override
            public Node apply(Node in) {
                Node [] operands = extractOperands(in);
                return new NodeExpr(
                    StandardOperation.AND,
                    new NodeExpr(StandardOperation.NOT,
                        new NodeExpr(StandardOperation.LESS, operands)),
                    new NodeExpr(StandardOperation.NOT,
                        new NodeExpr(StandardOperation.EQ, operands)));
            }
        };
        ruleset.put(rule.getOperationId(), rule);
   
        rule = new ExpressionRule(StandardOperation.GREATEREQ) {
            @Override
            public Node apply(Node in) {
                return new NodeExpr(
                    StandardOperation.NOT,
                    new NodeExpr(StandardOperation.LESS, extractOperands(in)));
            }
        };
        ruleset.put(rule.getOperationId(), rule);

        rule = new ExpressionRule(StandardOperation.BVULE) {
            @Override
            public Node apply(Node in) {
                Node[] operands = extractOperands(in);
                return new NodeExpr(
                    StandardOperation.OR,
                    new NodeExpr(StandardOperation.BVULT, operands),
                    new NodeExpr(StandardOperation.EQ, operands));
            }
        };
        ruleset.put(rule.getOperationId(), rule);

        rule = new ExpressionRule(StandardOperation.BVUGE) {
            @Override
            public Node apply(Node in) {
                return new NodeExpr(
                    StandardOperation.NOT,
                    new NodeExpr(StandardOperation.BVULT, extractOperands(in)));
            }
        };
        ruleset.put(rule.getOperationId(), rule);

        rule = new ExpressionRule(StandardOperation.BVUGT) {
            @Override
            public Node apply(Node in) {
                Node [] operands = extractOperands(in);
                return new NodeExpr(
                    StandardOperation.AND,
                    new NodeExpr(StandardOperation.NOT,
                        new NodeExpr(StandardOperation.BVULT, operands)),
                    new NodeExpr(StandardOperation.NOT,
                        new NodeExpr(StandardOperation.EQ, operands)));
            }
        };
        ruleset.put(rule.getOperationId(), rule);

        rule = new ExpressionRule(StandardOperation.BVSLE) {
            @Override
            public Node apply(Node in) {
                Node[] operands = extractOperands(in);
                return new NodeExpr(
                    StandardOperation.OR,
                    new NodeExpr(StandardOperation.BVSLT, operands),
                    new NodeExpr(StandardOperation.EQ, operands));
            }
        };
        ruleset.put(rule.getOperationId(), rule);

        rule = new ExpressionRule(StandardOperation.BVSGE) {
            @Override
            public Node apply(Node in) {
                return new NodeExpr(
                    StandardOperation.NOT,
                    new NodeExpr(StandardOperation.BVSLT, extractOperands(in)));
            }
        };
        ruleset.put(rule.getOperationId(), rule);

        rule = new ExpressionRule(StandardOperation.BVSGT) {
            @Override
            public Node apply(Node in) {
                Node [] operands = extractOperands(in);
                return new NodeExpr(
                    StandardOperation.AND,
                    new NodeExpr(StandardOperation.NOT,
                        new NodeExpr(StandardOperation.BVSLT, operands)),
                    new NodeExpr(StandardOperation.NOT,
                        new NodeExpr(StandardOperation.EQ, operands)));
            }
        };
        ruleset.put(rule.getOperationId(), rule);
        return ruleset;
    }
}
