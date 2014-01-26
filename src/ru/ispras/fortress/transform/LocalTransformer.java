package ru.ispras.fortress.transform;

import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.IdentityHashMap;

import ru.ispras.fortress.expression.*;

public class LocalTransformer implements Visitor
{
    // TODO use list of rules for enum as priority queue
    private final Map<Enum<?>, TransformRule> ruleset;

    private final List<Node[]>  operandStack;
    private final List<Node>    exprStack;
    private final List<Node>    result;

    private Node rootNode;

    public LocalTransformer()
    {
        ruleset         = new IdentityHashMap<Enum<?>, TransformRule>();
        operandStack    = new ArrayList<Node[]>();
        exprStack       = new ArrayList<Node>();
        result          = new ArrayList<Node>();
        rootNode        = null;
    }

    public LocalTransformer(Map<Enum<?>, TransformRule> rules)
    {
        if (rules == null)
            throw new NullPointerException();

        ruleset         = new IdentityHashMap<Enum<?>, TransformRule>(rules);
        operandStack    = new ArrayList<Node[]>();
        exprStack       = new ArrayList<Node>();
        result          = new ArrayList<Node>();
        rootNode        = null;
    }

    public void addRule(Enum<?> opId, TransformRule rule)
    {
        if (opId == null || rule == null)
            throw new NullPointerException();

        // TODO check for replacements or/and add to end of queue
        ruleset.put(opId, rule);
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
        final Enum<?> opId = expr.getOperationId();

        // TODO consequtive rule application
        TransformRule rule = ruleset.get(opId);
        if (rule != null && rule.isApplicable(expr))
            exprStack.add(rule.apply(new NodeExpr(opId, operandStack.remove(pos))));
        else
        {
            exprStack.add(expr);
            operandStack.remove(pos);
        }
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
        // TODO apply rules to values
        if (rootNode == null)
            rootNode = value;
    }

    @Override
    public void onVariable(NodeVariable variable)
    {
        // TODO apply rules to variables
        if (rootNode == null)
            rootNode = variable;
    }
}
