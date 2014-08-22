/*
 * Copyright (c) 2014 ISPRAS (www.ispras.ru)
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * XMLConstraintHandler.java, Mar 21, 2014 5:21:03 PM Andrei Tatarnikov
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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;
import java.util.Collections;

import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.NodeBinding;
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

    private final Map<String, Variable> incompleteScope = new HashMap<String, Variable>();
    private VariableScope nestedScope = VariableScope.EMPTY_SCOPE;

    private static class VariableScope
    {
        public final static VariableScope EMPTY_SCOPE = new VariableScope() {
            @Override
            public boolean contains(String name) {
                return false;
            }

            @Override
            public Variable get(String name) {
                return null;
            }
        };

        private final Map<String, Variable> variables;
        private final VariableScope hidden;

        private VariableScope()
        {
            this.variables = Collections.emptyMap();
            this.hidden = null;
        }

        public VariableScope(VariableScope previous, Map<String, Variable> variables)
        {
            this.variables = variables;
            this.hidden = previous;
        }

        public VariableScope getHiddenScope()
        {
            return hidden;
        }

        public boolean contains(String name)
        {
            if (variables.containsKey(name))
                return true;

            return hidden.contains(name);
        }

        public Variable get(String name)
        {
            if (variables.containsKey(name))
                return variables.get(name);

            return hidden.get(name);
        }
    }

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
                builder.beginInnerRep();
                break;
            }

            case FORMULA:
            {
                builder.beginFormula();
                break;
            }

            case OPERATION:
            {
                builder.beginOperation();
                builder.pushOperation(getOperationId(qName, attributes));
                break;
            }

            case VARIABLE_REF:
            {
                final String variableName = getVariableRef(qName, attributes);

                if (nestedScope.contains(variableName))
                    builder.pushElement(new NodeVariable(nestedScope.get(variableName)));
                else if (variables.containsKey(variableName))
                    builder.pushElement(new NodeVariable(variables.get(variableName)));
                else
                    throw new SAXException(String.format(Messages.ERR_UNDEFINED_VARIABLE, variableName));

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

            case BINDING:
            {
                builder.beginBinding();
                break;
            }

            case BOUND_VARIABLE:
            {
                final String variableName = getVariableRef(qName, attributes);
                final Variable variable = createLocalVariable(variableName);

                incompleteScope.put(variableName, variable);
                builder.pushElement(new NodeVariable(variable));

                break;
            }

            case BINDING_LIST:
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
            throw new SAXException(Messages.ERR_INVALID_CONSTRAINT + e.getMessage(), e);
        }

        /////////// DEBUG CODE ////////////////////////
        //System.out.print("<" + qName + ">");
        //for (int index = 0; index < attributes.getLength(); ++index)
        //{
        //    System.out.print(" " + attributes.getLocalName(index) +
        //                     "=\"" + attributes.getValue(index) + "\" ");
        //}
    }

    private Variable createLocalVariable(String name)
    {
        return new Variable(name, DataType.UNKNOWN);
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
                builder.endInnerRep();
                break;

            case FORMULA:
                builder.endFormula();
                break;

            case OPERATION:
                builder.endOperation();
                break;

            case SIGNATURE:
                builder.endSignature();
                break;

            case BINDING:
                builder.endBinding();
                popVariableScope();
                break;

            case BINDING_LIST:
                pushVariableScope();
                break;

            case NAME:
            case KIND:
            case DESCRIPTION:
            case VARIABLE_REF:
            case VALUE:
            case VARIABLE:
            case BOUND_VARIABLE:
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
            throw new SAXException(Messages.ERR_INVALID_CONSTRAINT + e.getMessage(), e);
        }

        /////////// DEBUG CODE ////////////////////////
        //System.out.print("</" + qName + ">");
    }

    private void pushVariableScope()
    {
        nestedScope = new VariableScope(
            nestedScope,
            new HashMap<String, Variable>(incompleteScope));

        incompleteScope.clear();
    }

    private void popVariableScope()
    {
        nestedScope = nestedScope.getHiddenScope();
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
    private Formulas            formulas = null;
    private Node                 formula = null;

    private final Stack<OperationBuilder> operations =
        new Stack<OperationBuilder>();

    private void cleanup()
    {
        constraint = null;
        kind       = null;
        name       = null;

        formulas   = null; 
        formula    = null;

        operations.clear();
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

    public void beginInnerRep() throws Exception
    {
        if (null != formulas)
            throw new IllegalStateException(
                String.format(Messages.ERR_ALREADY_STARTED, "InnerRep"));

        formulas = new Formulas();
    }

    public void endInnerRep() throws Exception
    {
        // Nothing
    }

    public void beginFormula() throws Exception
    {
        if (null != formula)
            throw new IllegalStateException(
                 String.format(Messages.ERR_ALREADY_STARTED, "Formula"));

        formula = null;
    }

    public void endFormula() throws Exception
    {
        formulas.add(formula);
        formula = null;
    }

    public void beginOperation() throws Exception
    {
        operations.push(new OperationBuilder());
    }

    public void endOperation() throws Exception
    {
        if (operations.empty())
            throw new IllegalStateException(Messages.ERR_NO_OPERATION);

        final NodeOperation expr = operations.pop().create();

        if (operations.empty())
        {
            if (null != formula)
                throw new IllegalStateException(
                    Messages.ERR_FORMULA_ALREADY_ASSIGNED);

            formula = expr;
        }
        else
        {
            pushElement(expr);
        }
    }

    public void beginBinding() throws Exception
    {
        operations.push(new OperationBuilder());
    }

    public void endBinding() throws Exception
    {
        if (operations.empty())
            throw new IllegalStateException(Messages.ERR_NO_OPERATION);

        final NodeBinding node = operations.pop().createBinding();

        if (operations.empty())
        {
            if (null != formula)
                throw new IllegalStateException(
                    Messages.ERR_FORMULA_ALREADY_ASSIGNED);

            formula = node;
        }
        else
            pushElement(node);
    }

    public void pushElement(Node se) throws Exception
    {
        if (operations.empty())
        {
            if (null != formula)
                throw new IllegalStateException(
                     Messages.ERR_FORMULA_ALREADY_ASSIGNED);

            formula = se;
        }
        else
        {
            operations.lastElement().addElement(se);
        }
    }

    public void pushOperation(Enum<?> oid) throws Exception
    {
        if (operations.empty())
            throw new IllegalStateException(String.format(
                Messages.ERR_NO_EXPRESSION_FOR_OP, oid.name()));

        operations.lastElement().setOperationId(oid);
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
        constraint.setInnerRep(formulas);
        return constraint.build();
    }
}

/**
 * The OperationBuilder class is aimed to build an operation expression
 * from its attributes (operation and operands).
 *
 * @author Andrei Tatarnikov
 */

final class OperationBuilder
{
    private Enum<?>       operationId;
    private final List<Node> elements;

    public OperationBuilder()
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

    public NodeOperation create() throws Exception
    {
        if (null == operationId)
            throw new Exception(Messages.ERR_NO_OPERATION_ID);

        return new NodeOperation(operationId, elements.toArray(new Node[] {}));
    }

    public NodeBinding createBinding() throws Exception
    {
        final Node expr = elements.remove(elements.size() - 1);
        final List<NodeBinding.BoundVariable> bindings =
            new ArrayList<NodeBinding.BoundVariable>();

        for (int i = 0; i < elements.size(); i += 2)
        {
            if (!(elements.get(i) instanceof NodeVariable))
                throw new Exception("NodeVariable expected");

            final NodeVariable var = (NodeVariable) elements.get(i);
            bindings.add(NodeBinding.bindVariable(var, elements.get(i + 1)));
        }
        return new NodeBinding(expr, bindings);
    }
}
