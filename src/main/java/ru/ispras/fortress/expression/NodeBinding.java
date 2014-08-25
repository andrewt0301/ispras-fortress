package ru.ispras.fortress.expression;

import java.util.Arrays;
import java.util.List;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.Collections;

import ru.ispras.fortress.data.DataType;

/**
 * The NodeBinding class represents set of substitutions to be considered
 * in underlying expression subtree. List of bound variables considered
 * immutable.
 */

public final class NodeBinding extends Node
{
    /**
    * The BoundVariable class represents key-value binding pair.
    */
    public final static class BoundVariable
    {
        private final NodeVariable variable;
        private final Node value;

        private BoundVariable(NodeVariable variable, Node value)
        {
            this.variable = variable;
            this.value = value;
        }

        /**
         * Returns object representing bound variable.
         * 
         *  @return A bound variable object reference.
         */

        public NodeVariable getVariable()
        {
            return variable;
        }

        /**
         * Returns bound value object.
         * 
         *  @return A bound value.
         */

        public Node getValue()
        {
            return value;
        }

        @Override
        public int hashCode()
        {
            final int prime = 31;
            return prime * variable.hashCode() + value.hashCode();
        }

        @Override
        public boolean equals(Object rhs)
        {
            if (rhs == null)
                return false;

            if (rhs == this)
                return true;

            if (this.getClass() != rhs.getClass())
                return false;
            
            final BoundVariable binding = (BoundVariable) rhs;
            return variable.equals(binding.variable) && value.equals(binding.value);
        }
    }

    private Node expr;
    private List<BoundVariable> bindings;

    /**
     * Creates a node based on expression and list of bindings.
     * List of bound variables considered immutable therefore incurring
     * need for copying input list. List is sorted because equality
     * comparison relies on order of bindings.
     *
     * @param expression Expression subtree.
     * @param bindings List of bound variables.
     */

    public NodeBinding(Node expression, List<BoundVariable> bindings)
    {
        super(Kind.BINDING);

        if (expression == null)
            throw new NullPointerException();

        if (bindings == null)
            throw new NullPointerException();

        this.expr = expression;

        if (bindings.isEmpty())
            this.bindings = Collections.emptyList();
        else
            this.bindings = new ArrayList<BoundVariable>(bindings);

        final Comparator<BoundVariable> cmp = new Comparator<BoundVariable>()
        {
            public int compare(BoundVariable lhs, BoundVariable rhs)
            {
                if (lhs == null)
                    throw new NullPointerException();

                if (rhs == null)
                    throw new NullPointerException();

                return lhs.getVariable().getName().compareTo(rhs.getVariable().getName());
            }
        };

        Collections.sort(this.bindings, cmp);
    }

    /**
     * Constructs a node based on an expression and a variable number
     * of bindings. See constructor <code>
     * NodeBinding(Node expression, List<BoundVariable> bindings)</code>.
     * 
     * @param expression Expression subtree.
     * @param bindings Bound variables.
     */

    public NodeBinding(Node expression, BoundVariable ... bindings)
    {
        this(expression, Arrays.asList(bindings));
    }

    /**
     * Constructor to avoid redundant allocations. Do not incur sorting.
     * 
     * @param expr Expression subtree.
     * @param bindings List of bound variables.
     */

    private NodeBinding(Node expr, List<BoundVariable> bindings, int unused)
    {
        super(Kind.BINDING);

        this.expr = expr;
        this.bindings = bindings;
    }

    /**
     * Returns list of bound variables associated with the node.
     * 
     * @return Unmodifiable list of bound variables.
     */

    public List<BoundVariable> getBindings()
    {
        return Collections.unmodifiableList(bindings);
    }

    /**
     * Returns underlying expression subtree.
     * 
     * @return An expression.
     */

    public Node getExpression()
    {
        return expr;
    }

    /**
     * {@inheritDoc}
     */

    public Node deepCopy()
    {
        return new NodeBinding(this.expr, this.bindings, 0);
    }

    /**
     * Create binding node with same bindings for given expression.
     * Avoids additional costs of using constructor directly.
     * 
     * @param expression An expression subtree.
     *
     * @return A binding node object.
     */

    public NodeBinding bindTo(Node expression)
    {
        return new NodeBinding(expression, this.bindings, 0);
    }

    /**
     * Create bound variable using NodeVariable object and expression.
     * 
     * @param variable An object representing bound variable.
     * @param value A bound value.
     *
     * @return A bound variable object.
     */

    public static BoundVariable bindVariable(NodeVariable variable, Node value)
    {
        if (variable == null)
            throw new NullPointerException();
        if (value == null)
            throw new NullPointerException();

        return new BoundVariable(variable, value);
    }

    /**
     * {@inheritDoc}
     */

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
        builder.append(")");

        return builder.toString();
    }

    @Override
    public int hashCode()
    {
        final int prime = 31;
        return expr.hashCode() * prime + bindings.hashCode();
    }

    @Override
    public boolean equals(Object rhs)
    {
        if (rhs == null)
            return false;

        if (rhs == this)
            return true;

        if (this.getClass() != rhs.getClass())
            return false;

        final NodeBinding node = (NodeBinding) rhs;
        return this.bindings.equals(node.bindings);
    }
}
