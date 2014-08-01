package ru.ispras.fortress.transformer;

import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.HashMap;
import java.util.IdentityHashMap;

import ru.ispras.fortress.expression.*;

public class NodeTransformer implements ExprTreeVisitor
{
    // TODO use list of rules for enum as priority queue
    private final Map<Enum<?>, TransformerRule> ruleset;

    private final List<Node[]>  operandStack;
    private final List<Node>    exprStack;
    private final List<Node>    result;
    private final List<NodeBinding.BoundVariable> boundStack;

    public void walk(Node root)
    {
        final ExprTreeWalker walker = new ExprTreeWalker(this);
        walker.visit(root);
    }

    public void walk(Iterable<Node> trees)
    {
        final ExprTreeWalker walker = new ExprTreeWalker(this);
        walker.visit(trees);
    }

    public NodeTransformer()
    {
        this(new IdentityHashMap<Enum<?>, TransformerRule>());
    }

    public NodeTransformer(Map<Enum<?>, TransformerRule> rules)
    {
        if (rules == null)
            throw new NullPointerException();

        ruleset         = new IdentityHashMap<Enum<?>, TransformerRule>(rules);
        operandStack    = new ArrayList<Node[]>();
        exprStack       = new ArrayList<Node>();
        result          = new ArrayList<Node>();
        boundStack      = new ArrayList<NodeBinding.BoundVariable>();
    }

    public void addRule(Enum<?> opId, TransformerRule rule)
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
        final TransformerRule rule = ruleset.get(id);
        if (rule != null && rule.isApplicable(node))
            return rule.apply(node);
        return node;
    }

    private final Node updateNode(Node node)
    {
        return applyRule(node.getKind(), node);
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
        assert exprStack.size() == 1;
        result.add(exprStack.remove(0));
    }

    @Override
    public void onExprBegin(NodeExpr expr)
    {
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
        operands[index] = exprStack.remove(exprStack.size() - 1);
    }

    @Override
    public void onValue(NodeValue value)
    {
        exprStack.add(value);
    }

    @Override
    public void onVariable(NodeVariable variable)
    {
        exprStack.add(updateNode(variable));
    }

    @Override
    public void onBindingBegin(NodeBinding node)
    {
    }

    @Override
    public void onBindingListEnd(NodeBinding node)
    {
        final int fromIndex = boundStack.size() - node.getBindings().size();
        final List<NodeBinding.BoundVariable> bindings =
            boundStack.subList(fromIndex, boundStack.size());

        final TransformerRule scopedRule =
            new RejectBoundVariablesRule(
                ruleset.get(Node.Kind.VARIABLE),
                new NodeBinding(node.getExpression(), bindings));

        ruleset.put(Node.Kind.VARIABLE, scopedRule);
        bindings.clear();
    }

    @Override
    public void onBindingEnd(NodeBinding node)
    {
        final RejectBoundVariablesRule rule =
            (RejectBoundVariablesRule) ruleset.get(Node.Kind.VARIABLE);
        ruleset.put(Node.Kind.VARIABLE, rule.getShadowedRule());

        final Node expr = exprStack.remove(exprStack.size() - 1);
        final NodeBinding bindingNode = rule.getBinding().bindTo(expr);
        exprStack.add(updateNode(bindingNode));
    }

    @Override
    public void onBoundVariableBegin(NodeBinding node, NodeVariable variable, Node value) {}

    @Override
    public void onBoundVariableEnd(NodeBinding node, NodeVariable variable, Node value)
    {
        final Node updatedValue = exprStack.remove(exprStack.size() - 1);
        boundStack.add(NodeBinding.bindVariable(variable, updatedValue));
    }
}

abstract class ScopedBindingRule implements TransformerRule
{
    protected final TransformerRule   shadowed;
    protected final Map<String, Node> bindings;
    protected Node applicableCache;

    public ScopedBindingRule(TransformerRule previous, List<NodeBinding.BoundVariable> bindingList)
    {
        this.shadowed = previous;
        this.bindings = new HashMap<String, Node>();
        for (NodeBinding.BoundVariable bound : bindingList)
            bindings.put(bound.getVariable().getName(), bound.getValue());
        this.applicableCache = null;
    }

    @Override
    public Node apply(Node node)
    {
        return applicableCache;
    }

    public TransformerRule getShadowedRule()
    {
        return shadowed;
    }
}

final class RejectBoundVariablesRule extends ScopedBindingRule
{
    private final NodeBinding node;

    public RejectBoundVariablesRule(TransformerRule previous, NodeBinding node)
    {
        super(previous, node.getBindings());
        this.node = node;
    }

    public NodeBinding getBinding()
    {
        return node;
    }

    @Override
    public boolean isApplicable(Node node)
    {
        if (node.getKind() != Node.Kind.VARIABLE)
            return false;

        final NodeVariable variable = (NodeVariable) node;

        // variable is bound
        if (bindings.containsKey(variable.getName()))
            return false;

        if (shadowed == null)
            return false;

        boolean applicable = shadowed.isApplicable(node);
        if (applicable)
            applicableCache = shadowed.apply(node);
        return applicable;
    }
}
