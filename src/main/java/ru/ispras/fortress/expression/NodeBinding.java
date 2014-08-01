package ru.ispras.fortress.expression;

import java.util.List;
import java.util.ArrayList;
import java.util.Collections;

import ru.ispras.fortress.data.DataType;

public final class NodeBinding extends Node
{
    public final static class BoundVariable
    {
        private final NodeVariable variable;
        private final Node value;

        private BoundVariable(NodeVariable variable, Node value)
        {
            this.variable = variable;
            this.value = value;
        }

        public NodeVariable getVariable()
        {
            return variable;
        }

        public Node getValue()
        {
            return value;
        }
    }

    private Node expr;
    private List<BoundVariable> bindings;

    public NodeBinding(Node expr, List<BoundVariable> bindings)
    {
        super(Kind.BINDING);

        if (expr == null)
            throw new NullPointerException();

        if (bindings == null)
            throw new NullPointerException();

        this.expr = expr;

        if (bindings.isEmpty())
            this.bindings = Collections.emptyList();
        else
            this.bindings = new ArrayList<BoundVariable>(bindings);
    }

    private NodeBinding(Node expr, List<BoundVariable> bindings, int unused)
    {
        super(Kind.BINDING);

        this.expr = expr;
        this.bindings = bindings;
    }

    public List<BoundVariable> getBindings()
    {
        return Collections.unmodifiableList(bindings);
    }

    public Node getExpression()
    {
        return expr;
    }

    public Node deepCopy()
    {
        return new NodeBinding(this.expr, this.bindings, 0);
    }

    public NodeBinding bindTo(Node expr)
    {
        return new NodeBinding(expr, this.bindings, 0);
    }

    public static BoundVariable bindVariable(NodeVariable variable, Node value)
    {
        if (variable == null)
            throw new NullPointerException();
        if (value == null)
            throw new NullPointerException();

        return new BoundVariable(variable, value);
    }

    @Override
    public DataType getDataType()
    {
        return expr.getDataType();
    }

    @Override
    public String toString()
    {
        final StringBuilder builder = new StringBuilder();

        builder.append("(LET (");
        for (BoundVariable bound : getBindings())
        {
            builder.append("(");
            builder.append(bound.getVariable().toString());
            builder.append(" ");
            builder.append(bound.getValue().toString());
            builder.append(")");
        }
        builder.append(") ");
        builder.append(getExpression().toString());

        return builder.toString();
    }
}
