package ru.ispras.fortress.transform;

import java.util.List;
import java.util.ArrayList;

import ru.ispras.fortress.expression.*;

public class PredicateTransformer implements Visitor
{
    public enum StandardRule
    {
        NOTEQ(StandardOperation.NOTEQ, new TransformRule() {
            @Override
            public Node apply(NodeExpr in) {
                return new NodeExpr(
                    StandardOperation.NOT,
                    new NodeExpr(StandardOperation.EQ, extractOperands(in)));
            }
        }),
    
        LESSEQ(StandardOperation.LESSEQ, new TransformRule() {
            @Override
            public Node apply(NodeExpr in)
            {
                Node[] operands = extractOperands(in);
                return new NodeExpr(
                    StandardOperation.OR,
                    new NodeExpr(StandardOperation.LESS, operands),
                    new NodeExpr(StandardOperation.EQ, operands));
            }
        }),
    
        GREATER(StandardOperation.GREATER, new TransformRule() {
            @Override
            public Node apply(NodeExpr in)
            {
                Node [] operands = extractOperands(in);
                return new NodeExpr(
                    StandardOperation.AND,
                    new NodeExpr(StandardOperation.NOT,
                        new NodeExpr(StandardOperation.LESS, operands)),
                    new NodeExpr(StandardOperation.NOT,
                        new NodeExpr(StandardOperation.EQ, operands)));
            }
        }),
    
        GREATEREQ(StandardOperation.GREATEREQ, new TransformRule() {
            @Override
            public Node apply(NodeExpr in)
            {
                return new NodeExpr(
                    StandardOperation.NOT,
                    new NodeExpr(StandardOperation.LESS, extractOperands(in)));
            }
        });

        private final StandardOperation op;
        private final TransformRule     rule;

        StandardRule(StandardOperation op, TransformRule rule)
        {
            this.op = op;
            this.rule = rule;
        }

        private static Node[] extractOperands(NodeExpr in)
        {
            Node[] operands = new Node[in.getOperandCount()];
            for (int i = 0; i < operands.length; ++i)
                operands[i] = in.getOperand(i);

            return operands;
        }

        public static Node apply(NodeExpr in)
        {
            for (StandardRule r : StandardRule.values())
                if (r.op == in.getOperationId())
                    return r.rule.apply(in);

            return in;
        }
    }

    private final List<Node[]>  operandStack;
    private final List<Node>    exprStack;
    private final List<Node>    result;
    private Node rootNode;

    PredicateTransformer()
    {
        operandStack = new ArrayList<Node[]>();
        exprStack = new ArrayList<Node>();
        result = new ArrayList<Node>();
        rootNode = null;
    }

    public Iterable<Node> getResult()
    {
        return result;
    }

    @Override
    public void onRootBegin() {}

    @Override
    public void onRootEnd()
    {
        if (exprStack.isEmpty())
            result.add(rootNode);
        else
        {
            assert exprStack.size() == 1;
            result.add(exprStack.remove(0));
        }
        rootNode = null;
    }

    @Override
    public void onExprBegin(NodeExpr expr)
    {
        if (rootNode == null)
            rootNode = expr;

        if (expr.getOperandCount() > 0)
            operandStack.add(new Node[expr.getOperandCount()]);
    }

    @Override
    public void onExprEnd(NodeExpr expr)
    {
        if (expr.getOperandCount() == 0)
        {
            exprStack.add(expr);
            return;
        }

        final int pos = operandStack.size() - 1;
        exprStack.add(
            StandardRule.apply(new NodeExpr(expr.getOperationId(), operandStack.remove(pos))));
    }

    @Override
    public void onOperandBegin(NodeExpr expr, Node operand, int index) {}

    @Override
    public void onOperandEnd(NodeExpr expr, Node operand, int index)
    {
        Node[] operands = operandStack.get(operandStack.size() - 1);
        if (operand.getKind() == Node.Kind.EXPR)
            operands[index] = exprStack.remove(exprStack.size() - 1);
        else
            operands[index] = operand;
    }

    @Override
    public void onValue(NodeValue value)
    {
        if (rootNode == null)
            rootNode = value;
    }

    @Override
    public void onVariable(NodeVariable variable)
    {
        if (rootNode == null)
            rootNode = variable;
    }
}
