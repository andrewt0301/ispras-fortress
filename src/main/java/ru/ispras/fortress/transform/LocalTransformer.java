package ru.ispras.fortress.transform;

import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.IdentityHashMap;

import ru.ispras.fortress.expression.*;

public class LocalTransformer implements ExprTreeVisitor
{
    // TODO use list of rules for enum as priority queue
    private final Map<Enum<?>, TransformRule> ruleset;

    private final List<Node[]>  operandStack;
    private final List<Node>    exprStack;
    private final List<Node>    result;

    private Node           rootNode;
    private ExprTreeWalker walker;

    public void walk(Node root)
    {
        walker = new ExprTreeWalker(this);
        walker.visit(root);
        walker = null;
    }

    public void walk(Iterable<Node> trees)
    {
        walker = new ExprTreeWalker(this);
        walker.visit(trees);
        walker = null;
    }

    public LocalTransformer()
    {
        this(new IdentityHashMap<Enum<?>, TransformRule>());
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
        walker          = null;
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

    private final Node applyRule(Enum<?> id, Node node)
    {
        TransformRule rule = ruleset.get(id);
        if (rule != null && rule.isApplicable(node))
            return rule.apply(node);
        return node;
    }

    @Override
    public Status getStatus()
    {
        // We are not going to stop the walker or to skip any subtrees.
        // At least, I (Andrei Tatarnikov) think so.
        // Therefore, it is always OK.

        return Status.OK;
    }

    @Override
    public void onRootBegin() {}

    @Override
    public void onRootEnd()
    {
        if (exprStack.isEmpty())
        {
            if (rootNode.getKind() != Node.Kind.EXPR)
                rootNode = applyRule(rootNode.getKind(), rootNode);
            result.add(rootNode);
        }
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
        Node node = applyRule(opId, new NodeExpr(opId, operandStack.remove(pos)));
        exprStack.add(node);
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
            operands[index] = applyRule(operand.getKind(), operand);
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
