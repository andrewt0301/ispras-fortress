/*
 * Copyright (c) 2013 ISPRAS (www.ispras.ru)
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * Node.java, Jun 24, 2013 12:30:00 PM Andrei Tatarnikov
 * 
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not
 * use this file except in compliance with the License. You may obtain a copy of
 * the License at
 * 
 * http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations under
 * the License.
 */

package ru.ispras.fortress.expression;

import javax.xml.bind.annotation.adapters.XmlJavaTypeAdapter;

import ru.ispras.fortress.data.DataType;
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
        EXPR,

        /** A binding node. Represents group of variable substitutions. */
        BINDING
    }

    private final Kind kind;
    private Object userData;

    /**
     * Creates a node of the specified kind.
     * @param kind Node kind identifier.
     * @throws NullPointerException if the parameter equals null.
     */

    protected Node(Kind kind)
    {
        if (null == kind)
            throw new NullPointerException();

        this.kind = kind;
    }

    /**
     * Constructor for making copies. The fields are copied by reference because
     * the kind field is immutable and the userData field is of an unknown type 
     * (there is no way to know how to clone it).
     *  
     * @param node Node object to be copied.
     * @throws NullPointerException if the parameter equals null.
     */

    protected Node(Node node)
    {
        if (null == node)
            throw new NullPointerException();

        this.kind = node.kind;
        this.userData = node.userData;
    }

    /**
     * Creates a deep copy of the current objects. All aggregated objects 
     * that are not readonly must be cloned. This excludes user data as 
     * its type is unknown.
     * @return Full copy of the current node object.
     */

    public abstract Node deepCopy(); 

    /**
     * Returns the identifier that specifies the kind of the node.
     * @return A node kind identifier.
     */

    public final Kind getKind()
    {
        return kind;
    }

    /**
     * Returns an object that describes the type of the value referred by the node.
     * 
     * @return A data type object.
     */

    public abstract DataType getDataType();

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
