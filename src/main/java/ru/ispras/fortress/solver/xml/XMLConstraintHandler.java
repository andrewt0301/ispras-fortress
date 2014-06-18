/*
 * Copyright (c) 2014 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * XMLConstraintHandler.java, Mar 21, 2014 5:21:03 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver.xml;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.DataTypeId;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeExpr;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintBuilder;
import ru.ispras.fortress.solver.constraint.ConstraintKind;
import ru.ispras.fortress.solver.constraint.Formulas;

/**
 * The XMLConstraintHandler class is handler for SAX parser events that
 * builds a constraint basing on its XML representation.
 *
 * @author Andrei Tatarnikov
 */

final class XMLConstraintHandler extends DefaultHandler
{
    private final XMLConstraintBuilder    builder = new XMLConstraintBuilder();
    private final Stack<XMLNodeType>        nodes = new Stack<XMLNodeType>();
    private final Map<String, Variable> variables = new HashMap<String, Variable>();

    public Constraint getConstraint()
    {
        return builder.getConstraint();
    }

    @Override
    public void startElement(String uri, String localName, String qName, Attributes attributes) throws SAXException
    {
        try
        {
            final XMLNodeType currentNode = getNodeType(qName);
            verifyNodeHierarchy(currentNode, nodes.empty() ? null : nodes.lastElement());

            switch (currentNode)
            {
            case CONSTRAINT:
            {
                nodes.clear();
                verifyFormatVersion(qName, attributes);
                builder.beginConstraint();
                break;
            }

            case INNER_REP:
            {
                builder.beginSyntax();
                break;
            }

            case FORMULA:
            {
                builder.beginFormula();
                break;
            }

            case EXPRESSION:
            {
                builder.beginExpression();
                break;
            }

            case OPERATION:
            {
                builder.pushOperation(getOperationId(qName, attributes));
                break;
            }

            case VARIABLE_REF:
            {
                final String variableName = getVariableRef(qName, attributes);

                if (!variables.containsKey(variableName))
                    throw new SAXException(String.format(Messages.ERR_UNDEFINED_VARIABLE, variableName));

                final Variable variable = variables.get(variableName);
                builder.pushElement(new NodeVariable(variable));

                break;
            }

            case VALUE:
            {
                final Data value = getValue(qName, attributes);
                builder.pushElement(new NodeValue(value));
                break;
            }

            case SIGNATURE:
            {
                builder.beginSignature();
                break;
            }

            case VARIABLE:
            {
                final Variable variable = builder.addGlobalVariable(getVariable(qName, attributes));
                variables.put(variable.getName(), variable);
                break;
            }

            case NAME:
            case KIND:
            case DESCRIPTION:
            {
                // Do nothing
                break;
            }

            default:
            {
                assert false;
                break;
            }
            }

            nodes.push(currentNode);
        }
        catch (SAXException e)
        {
            throw e;
        }
        catch (Exception e)
        {
            throw new SAXException(Messages.ERR_INVALID_CONSTRAINT + e.getMessage());
        }

        /////////// DEBUG CODE ////////////////////////
        //System.out.print("<" + qName + ">");
        //for (int index = 0; index < attributes.getLength(); ++index)
        //{
        //    System.out.print(" " + attributes.getLocalName(index) +
        //                     "=\"" + attributes.getValue(index) + "\" ");
        //}
    }

    @Override
    public void endElement(String uri, String localName, String qName) throws SAXException
    {
        assert !nodes.empty();
        try
        {
            final XMLNodeType currentNode = getNodeType(qName);
            assert (currentNode == nodes.lastElement());

            switch (currentNode)
            {
            case CONSTRAINT:
                builder.endConstraint();
                break;

            case INNER_REP:
                builder.endSyntax();
                break;

            case FORMULA:
                builder.endFormula();
                break;

            case EXPRESSION:
                builder.endExpression();
                break;

            case SIGNATURE:
                builder.endSignature();
                break;

            case NAME:
            case KIND:
            case DESCRIPTION:
            case OPERATION:
            case VARIABLE_REF:
            case VALUE:
            case VARIABLE:
                // Nothing
                break;

            default:
                assert false;
                break;
            }

            nodes.pop();
        }
        catch (SAXException e)
        {
            throw e;
        }
        catch (Exception e)
        {
            throw new SAXException(Messages.ERR_INVALID_CONSTRAINT + e.getMessage());
        }

        /////////// DEBUG CODE ////////////////////////
        //System.out.print("</" + qName + ">");
    }

    @Override
    public void characters(char ch[], int start, int length) throws SAXException
    {
        assert !nodes.empty();

        switch(nodes.lastElement())
        {
        case NAME:
            builder.setName(new String(ch, start, length));
            break;

        case KIND:
            builder.setKind(ConstraintKind.valueOf(new String(ch, start, length)));
            break;

        case DESCRIPTION:
            builder.setDescription(new String(ch, start, length));
            break;

        default:
            break;
        }

        /////////// DEBUG CODE ////////////////////////
        //System.out.print(new String(ch, start, length));
    }

    private static XMLNodeType getNodeType(String nodeName) throws SAXException
    {
        final XMLNodeType nodeType = XMLNodeType.fromNodeName(nodeName);

        if (null == nodeType)
            throw new SAXException(String.format(Messages.ERR_XML_UNKNOWN_NODE, nodeName));

       return nodeType;
    }

    private static String getAttribute(String nodeName, Attributes attributes, String attributeName) throws SAXException
    {
        final String attribute = attributes.getValue(attributeName);

        if (null == attribute)
            throw new SAXException(String.format(Messages.ERR_XML_NO_ATTRIBUTE, attributeName, nodeName));

        return attribute;
    }

    // XML representation: <Constraint version="1.0">
    private static void verifyFormatVersion(String nodeName, Attributes attributes) throws SAXException
    {
        final String versionString = getAttribute(nodeName, attributes, XMLConst.ATTR_FORMAT_VERSION);

        if (!versionString.matches("[\\d]+[.][\\d]+"))
            throw new SAXException(String.format(Messages.ERR_XML_BAD_ATTIBUTE, XMLConst.ATTR_FORMAT_VERSION, versionString, nodeName));

        final int majorVersion = Integer.valueOf(versionString.split("[.]")[0]);
        final int minorVersion = Integer.valueOf(versionString.split("[.]")[1]);

        if ((XMLFormatVersion.MAJOR != majorVersion) || (XMLFormatVersion.MINOR != minorVersion))
            throw new SAXException(String.format(Messages.ERR_XML_BAD_VERSION, majorVersion, minorVersion, XMLFormatVersion.MAJOR, XMLFormatVersion.MINOR));
    }

    private static void verifyNodeHierarchy(XMLNodeType current, XMLNodeType parent) throws SAXException
    {
        if (!current.isChildOf(parent))
        {
            throw new SAXException(String.format(Messages.ERR_XML_BAD_HIERARCHY,
                current.getNodeName(), parent.getNodeName()));
        }
    }

    // XML representation: <Value type="(BIT_VECTOR 3)" value="11"/>
    private static Data getValue(String nodeName, Attributes attributes) throws SAXException
    {
        final String typeIdString = getAttribute(nodeName, attributes, XMLConst.ATTR_TYPE_ID);
        final String  valueString = getAttribute(nodeName, attributes, XMLConst.ATTR_VALUE);
        final DataType   typeInfo = DataType.typeOf(typeIdString);

        return typeInfo.valueOf(valueString, typeInfo.getTypeRadix());
    }

    // XML representation: <Variable name="aaa" type="(BIT_VECTOR 3)" value=""/>
    private static Variable getVariable(String nodeName, Attributes attributes) throws SAXException
    {
        final String variableName = getAttribute(nodeName, attributes, XMLConst.ATTR_VARIABLE_NAME);
        final String typeIdString = getAttribute(nodeName, attributes, XMLConst.ATTR_TYPE_ID);
        final String  valueString = getAttribute(nodeName, attributes, XMLConst.ATTR_VALUE);

        final DataType typeInfo = DataType.typeOf(typeIdString);

        return valueString.isEmpty() ?
            new Variable(variableName, typeInfo) :
            new Variable(variableName, typeInfo.valueOf(valueString, typeInfo.getTypeRadix()));
    }

    // XML representation: <VariableRef name="aaa"/>
    private static String getVariableRef(String nodeName, Attributes attributes) throws SAXException
    {
        return getAttribute(nodeName, attributes, XMLConst.ATTR_VARIABLE_NAME);
    }

    // XML representation: <Operation id="BVAND"/>
    @SuppressWarnings({"unchecked", "rawtypes"})
    private static Enum<?> getOperationId(String nodeName, Attributes attributes) throws Exception
    {
        final String id = getAttribute(nodeName, attributes, XMLConst.ATTR_OPERATION_ID);
        final String family = getAttribute(nodeName, attributes, XMLConst.ATTR_OPERATION_FAMILY);

        final Class<?> idClass = Class.forName(family);
        return Enum.valueOf((Class<Enum>)idClass, id);
    }
}

/**
 * The XMLConstraintBuilder class implements functionality that build a constraint.
 *
 * @author Andrei Tatarnikov
 */

final class XMLConstraintBuilder
{
    private ConstraintBuilder constraint = null;
    private String                  name = null;
    private ConstraintKind          kind = null;
    private Formulas              syntax = null;
    private NodeExpr             formula = null;

    private final Stack<ExprBuilder> expressions =
        new Stack<ExprBuilder>();

    private void cleanup()
    {
        constraint  = null;
        kind        = null;
        name        = null;

        syntax      = null; 
        formula     = null;
        expressions.clear();
    }

    public void beginConstraint() throws Exception
    {
        cleanup();
        constraint = new ConstraintBuilder();
    }

    public void endConstraint() throws Exception
    {
        if (null == name)
            throw new Exception(Messages.ERR_NO_CONSTRAINT_NAME);

        if (null == kind)
            throw new Exception(Messages.ERR_NO_CONSTRAINT_KIND);
    }

    public void beginSignature() throws Exception
    {
        //
    }

    public void endSignature() throws Exception
    {
        //
    }

    public void beginSyntax() throws Exception
    {
        if (null != syntax)
            throw new Exception(Messages.ERR_SYNTAX_ALREADY_EXISTS);
        syntax = new Formulas();
    }

    public void endSyntax() throws Exception
    {
        // Nothing
    }

    public void beginFormula() throws Exception
    {
        assert null == formula;
        formula = null;
    }

    public void endFormula() throws Exception
    {
        syntax.add(formula);
        formula = null;
    }

    public void beginExpression() throws Exception
    {
        expressions.push(new ExprBuilder());
    }

    public void endExpression() throws Exception
    {
        assert !expressions.empty();

        NodeExpr operation = expressions.pop().create();
        if (expressions.empty())
            formula = operation;
        else
            pushElement(operation);
    }

    public void pushElement(Node se) throws Exception
    {
        assert !expressions.empty();
        expressions.lastElement().addElement(se);
    }

    public void pushOperation(Enum<?> oid) throws Exception
    {
        assert !expressions.empty();
        expressions.lastElement().setOperationId(oid);
    }

    public void setName(String name)
    {
        this.name = name;
    }

    public void setDescription(String description)
    {
        this.constraint.setDescription(description);
    }

    public void setKind(ConstraintKind kind)
    {
        this.kind = kind;
    }

    public Variable addGlobalVariable(Variable variable)
    {
        return constraint.addVariable(variable.getName(), variable.getData());
    }

    public Constraint getConstraint()
    {
        constraint.setName(name);
        constraint.setKind(kind);
        constraint.setInnerRep(syntax);
        return constraint.build();
    }
}

/**
 * The ExprBuilder class is aimed to build an expression from its attributes
 * (operation and two operands).
 *
 * @author Andrei Tatarnikov
 */

final class ExprBuilder
{
    private Enum<?>       operationId;
    private final List<Node> elements;

    public ExprBuilder()
    {
        this.operationId = null;
        this.elements    = new ArrayList<Node>();
    }

    public void setOperationId(Enum<?> operationId) throws Exception
    {
        if (null != this.operationId)
            throw new Exception(Messages.ERR_EXTRA_OPERATION_ID);

        this.operationId = operationId;
    }

    public void addElement(Node se) throws Exception
    {
        elements.add(se);
    }

    public NodeExpr create() throws Exception
    {
        if (null == operationId)
            throw new Exception(Messages.ERR_NO_OPERATION_ID);

        return new NodeExpr(operationId, elements.toArray(new Node[] {}));
    }
}
