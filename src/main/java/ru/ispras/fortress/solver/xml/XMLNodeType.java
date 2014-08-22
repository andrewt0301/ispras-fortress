/*
 * Copyright (c) 2012 ISPRAS (www.ispras.ru)
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * XMLNodeType.java, Jan 31, 2012 4:59:24 PM Andrei Tatarnikov
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

package ru.ispras.fortress.solver.xml;

import java.util.EnumSet;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

/**
 * The XMLNodeType enumeration describes XML nodes that correspond
 * to attributes of a constraint. It is used in the logic that parses
 * an XML document to build a constraint and checks its correctness.  
 * 
 * @author Andrei Tatarnikov
 */

enum XMLNodeType
{
    /**
     * The root node of the document. Contains all information describing
     * a constraint. Specifies the current format version as an attribute.
     * Contains child nodes. 
     */

    CONSTRAINT (XMLConst.NODE_CONSTRAINT),

    /**
     * Specifies the name of a constraint. A child of the Constraint node.
     * Contains text.
     */

    NAME (XMLConst.NODE_NAME),

    /**
     * Stores information about the constraint. A child of the Constraint node.
     * Contains text.
     */

    KIND (XMLConst.NODE_KIND),

    /**
     * Stores the description of a constraint. A child of the Constraint node.
     * Contains text.
     */

    DESCRIPTION (XMLConst.NODE_DESCRIPTION),

    /**
     * The root node for a tree describing the internal representation of
     * a constraint. For example, it can contain a list of formula expressions
     * that should be satisfied. 
     */

    INNER_REP (XMLConst.NODE_INNER_REP),

    /**
     * Specifies a logic formula (or an assertion) describing a condition
     * the constraint must satisfy.    
     */

    FORMULA (XMLConst.NODE_FORMULA),

    /**
     * Specifies the operation performed by operands of an expression. 
     */

    OPERATION (XMLConst.NODE_OPERATION),

    /**
     * Specifies a reference to a global variable which is used in an
     * expression as an operand.
     */

    VARIABLE_REF (XMLConst.NODE_VARIABLE_REF),

    /**
     * Specifies a value used in an expression as an operand.
     */

    VALUE (XMLConst.NODE_VALUE),

    /**
     * Describes the signature of a constraint including global variables. 
     */

    SIGNATURE (XMLConst.NODE_SIGNATURE),

    /**
     * Specifies a global variable.
     */

    VARIABLE (XMLConst.NODE_VARIABLE),

    /**
     * Specifies an expression with bound variables.
     */

    BINDING (XMLConst.NODE_BINDING),

    /**
     * Specifies a list of bound variables.
     */

    BINDING_LIST (XMLConst.NODE_BINDING_LIST),

    /**
     * Specifies a local variable is to be replaced in expression.
     */

    BOUND_VARIABLE (XMLConst.NODE_BOUND_VARIABLE);

    private static final Map<String, XMLNodeType> nameToTypeMap;
    static 
    {
        final Set<XMLNodeType> constraintSet =
            EnumSet.of(CONSTRAINT);

        final Set<XMLNodeType> nestingSet = 
            EnumSet.of(FORMULA, OPERATION, BINDING, BOUND_VARIABLE);

        CONSTRAINT.parents     = EnumSet.noneOf(XMLNodeType.class);
        NAME.parents           = constraintSet;
        KIND.parents           = constraintSet;
        DESCRIPTION.parents    = constraintSet;
        INNER_REP.parents      = constraintSet;
        FORMULA.parents        = EnumSet.of(INNER_REP);
        OPERATION.parents      = nestingSet;
        VARIABLE_REF.parents   = EnumSet.of(OPERATION);
        VALUE.parents          = nestingSet;
        SIGNATURE.parents      = constraintSet;
        VARIABLE.parents       = EnumSet.of(SIGNATURE);
        BINDING.parents        = nestingSet;
        BINDING_LIST.parents   = EnumSet.of(BINDING);
        BOUND_VARIABLE.parents = EnumSet.of(BINDING_LIST);

        nameToTypeMap = new HashMap<String, XMLNodeType>();
        for (XMLNodeType type : values())
        {
            if (null == type.parents)
                throw new NullPointerException(String.format(
                    "%s.parents is not initialized.", type.name()));

            nameToTypeMap.put(type.getNodeName(), type);
        }
    }

    private final String nodeName;
    private Set<XMLNodeType> parents;

    private XMLNodeType(String nodeName)
    {
        this.nodeName = nodeName;
        this.parents = null;
    }

    String getNodeName()
    {
        return nodeName;
    }

    boolean isChildOf(XMLNodeType parent)
    {
        if ((null == parent) && parents.isEmpty())
            return true;

        return parents.contains(parent);
    }

    static XMLNodeType fromNodeName(String name)
    {
        return nameToTypeMap.get(name);
    }
}
