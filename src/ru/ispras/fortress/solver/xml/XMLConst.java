/*
 * Copyright (c) 2012 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * XMLConst.java, Jan 31, 2012 4:58:21 PM Andrei Tatarnikov 
 */

package ru.ispras.fortress.solver.xml;

/**
 * The XMLFormatVersion class stores information about the current version
 * of the storage format. 
 * 
 * @author Andrei Tatarnikov
 */

class XMLFormatVersion
{
    private XMLFormatVersion() {}

    static final int MAJOR = 1;
    static final int MINOR = 0;
}

/**
 * The XMLConst class stores string constants related to an XML representation
 * of a constraint.
 * 
 * @author Andrei Tatarnikov
 */

class XMLConst
{
    private XMLConst() {}

    static final String NODE_CONSTRAINT       = "Constraint";
    static final String NODE_NAME             = "Name";
    static final String NODE_KIND             = "Kind";
    static final String NODE_DESCRIPTION      = "Description";
    static final String NODE_INNER_REP        = "InnerRep";
    static final String NODE_FORMULA          = "Formula";
    static final String NODE_EXPRESSION       = "Expression";
    static final String NODE_OPERATION        = "Operation";
    static final String NODE_VARIABLE         = "Variable";
    static final String NODE_VARIABLE_REF     = "VariableRef";
    static final String NODE_VALUE            = "Value";
    static final String NODE_SIGNATURE        = "Signature";

    static final String ATTR_FORMAT_VERSION   = "version";
    static final String ATTR_OPERATION_ID     = "id";
    static final String ATTR_VARIABLE_NAME    = "name";
    static final String ATTR_TYPE_ID          = "type";
    static final String ATTR_VALUE            = "value";
    static final String ATTR_DATA_LENGTH      = "length";
    static final String ATTR_OPERATION_FAMILY = "family";
}

/**
 * The Messages class stores string constants used in exceptions. 
 * 
 * @author Andrei Tatarnikov
 */

class Messages
{
    private Messages() {}

    static final String ERR_XML_UNKNOWN_NODE      = "The \"%s\" node is unexpected in the document.";
    static final String ERR_XML_NO_ATTRIBUTE      = "The \"%s\" attribute is not found (the \"%s\" node).";
    static final String ERR_XML_BAD_ATTIBUTE      = "The \"%s\" attribute has an invalid value %s (the \"%s\" node).";
    static final String ERR_XML_BAD_VERSION       = "Wrong format version. It is %d.%d while %d.%d is expected.";
    static final String ERR_XML_BAD_HIERARCHY     = "Wrong node hierarchy. The \"%s\" node cannot be a child of the \"%s\" node.";

    static final String ERR_INVALID_CONSTRAINT    = "Invalid constraint. "; 
    static final String ERR_BAD_CONSTRAINT_KIND   = "Unsupported constraint kind: ";
    static final String ERR_NO_CONSTRAINT_NAME    = "The constraint name is not specified.";
    static final String ERR_NO_CONSTRAINT_KIND    = "The constraint kind is not specified.";
    static final String ERR_SYNTAX_ALREADY_EXISTS = "Syntax already exists.";
    
    static final String ERR_NO_OPERATION_ID       = "The operation type is not specified.";
    static final String ERR_EXTRA_OPERATION_ID    = "The operation type is already set.";
    
    static final String ERR_UNDEFINED_VARIABLE    = "The \"%s\" variable cannot be appended to the expression. It is absent from the variable definition list.";
}
