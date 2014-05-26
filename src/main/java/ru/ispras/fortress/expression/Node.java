/*
 * Copyright (c) 2013 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * Node.java, Jun 24, 2013 12:30:00 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.expression;

import javax.xml.bind.annotation.adapters.XmlJavaTypeAdapter;

import ru.ispras.fortress.jaxb.JaxbNodeAdapter;

/**
 * The Node class is a base class for all kinds of classes describing nodes
 * in an expression tree. It includes declarations and implementations of 
 * methods common for all node kinds.
 *
 * @author Andrei Tatarnikov
 */

@XmlJavaTypeAdapter(JaxbNodeAdapter.class)
public abstract class Node
{
    /**
     * The Node.Kind enumeration specifies the kind of an expression tree node.
     * 
     * @author Andrei Tatarnikov
     */

    public static enum Kind
    {
        /** A value node. Stores a constant value. */
        VALUE,

        /** A variable node. Can be either an unknown variable or a named constant. */
        VARIABLE,

        /** An expression node. Describes an expression that includes an operation and one or two operands. */
        EXPR
    }

    private final Kind elementId;
    private Object      userData;

    protected Node(Kind kind)
    {
        this.elementId = kind;
    }

    /**
     * Returns the identifier that specifies the kind of the node.
     * @return A node kind identifier.
     */

    public final Kind getKind()
    {
        return elementId;
    }

    /**
     * Returns an object that describes the type of the value referred by the node.
     * TODO: Not implemented in the current version. Probably, will be implemented and
     * used in the future.  
     * 
     * @return A data type object.
     *
     * public abstract DataType getDataType();
     */

    /**
     * Associates a user data object with the current node
     * @param obj User data object.
     */

    public final void setUserData(Object obj)
    {
        this.userData = obj;
    }

    /**
     * Returns user data.
     * @return User data object.
     */

    public final Object getUserData()
    {
        return userData;
    }
    
    /**
     * Creates an expression by performing logic conjunction on two existing expressions.
     * 
     * @param left An existing expression.
     * @param right An existing expression.
     * @return A new expression.
     */

    public static Node AND(Node left, Node right)
    {
        if (null == left)
            throw new NullPointerException();

        if (null == right)
            throw new NullPointerException();

        return new NodeExpr(StandardOperation.AND, left, right);
    }

    /**
     * Creates a new expression by performing logic disjunction on two existing expressions.
     * 
     * @param left An existing expression.
     * @param right An existing expression.
     * @return A new expression.
     */

    public static Node OR(Node left, Node right)
    {
        if (null == left)
            throw new NullPointerException();

        if (null == right)
            throw new NullPointerException();

        return new NodeExpr(StandardOperation.OR, left, right);
    }

    /**
     * Creates a new expression by performing logical negation on an existing expression.
     * 
     * @param expr An existing expression.
     * @return A new expression.
     */

    public static Node NOT(Node expr)
    {
        if (null == expr)
            throw new NullPointerException();

        return new NodeExpr(StandardOperation.NOT, expr);
    }
}
