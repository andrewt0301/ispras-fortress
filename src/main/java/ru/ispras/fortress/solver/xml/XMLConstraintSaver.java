/*
 * Copyright (c) 2012 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * XMLConstraintSaver.java, Feb 1, 2012 12:04:36 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver.xml;

import java.io.File;
import java.util.Deque;
import java.util.LinkedList;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.w3c.dom.Document;
import org.w3c.dom.Element;


import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.*;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintKind;
import ru.ispras.fortress.solver.constraint.Formulas;


/**
 * The XMLConstraintSaver class provides functionality to save a constraint
 * with all its attributes to an XML file. 
 * 
 * @author Andrei Tatarnikov
 */

public final class XMLConstraintSaver
{
    private final String      fileName;
    private final Constraint constraint;

    private Document document;

    /**
     * Constructs an XMLConstraintSaver object that saves the specified
     * constraint to the specified XML document. 
     * 
     * @param fileName Target XML document file name.
     * @param constraint Constraint to be save.
     * 
     * @throws NullPointerException if any of the parameters equals null.
     * @throws IllegalArgumentException if the constraint is not formula-based
     * (its type is not FORMULA_BASED). Currently, the possibility of saving 
     * other constraint types is not implementeed. 
     */

    public XMLConstraintSaver(String fileName, Constraint constraint)
    {
        if (null == fileName)
            throw new NullPointerException();

        if  (null == constraint)
            throw new NullPointerException();

        if (ConstraintKind.FORMULA_BASED != constraint.getKind())
            throw new IllegalArgumentException(Messages.ERR_BAD_CONSTRAINT_KIND + constraint.getKind());

        this.fileName   = fileName;
        this.constraint = constraint;
        this.document   = null;
    }

    /**
     * Saves the specified constraint object to an XML file.
     * 
     * @param fileName The name of the target file.
     * @param constraint A constraint object to be saved.
     * @throws XMLNotSavedException 
     */
    
    public void save() throws XMLNotSavedException  
    {
        try
        {
            document = newDocument();

            final Element root = newConstraintElement();
            document.appendChild(root);

            root.appendChild(newTextBasedElement(XMLConst.NODE_NAME, constraint.getName()));
            root.appendChild(newTextBasedElement(XMLConst.NODE_KIND, constraint.getKind().name()));
            root.appendChild(newTextBasedElement(XMLConst.NODE_DESCRIPTION, constraint.getDescription()));
            root.appendChild(newSignatureElement());

            final Element innerRep = document.createElement(XMLConst.NODE_INNER_REP);
            root.appendChild(innerRep);

            final Walker walker = new Walker(new XMLBuilderForExprs(document, innerRep));
            walker.visit(((Formulas) constraint.getInnerRep()).exprs());

            saveDocument(document, fileName);
        }
        catch (Exception e)
        {
            throw new XMLNotSavedException(fileName, e);
        }
        finally
        {
            document = null;
        }
    }

    private static Document newDocument() throws ParserConfigurationException
    {
        final DocumentBuilderFactory docFactory = DocumentBuilderFactory.newInstance();
        final DocumentBuilder        docBuilder = docFactory.newDocumentBuilder();

        return docBuilder.newDocument();
    }

    private static void saveDocument(Document document, String fileName) throws TransformerConfigurationException, TransformerException
    {
        final DOMSource source = new DOMSource(document);
        final StreamResult streamResult = new StreamResult(new File(fileName));

        newTransformer().transform(source, streamResult);
    }

    private static Transformer newTransformer() throws TransformerConfigurationException
    {
        final TransformerFactory transformerFactory = TransformerFactory.newInstance();
        final Transformer transformer = transformerFactory.newTransformer();

        transformer.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "no");
        transformer.setOutputProperty(OutputKeys.METHOD, "xml");
        transformer.setOutputProperty(OutputKeys.INDENT, "yes");
        transformer.setOutputProperty(OutputKeys.ENCODING, "UTF-8");
        transformer.setOutputProperty("{http://xml.apache.org/xslt}indent-amount", "4");

        return transformer;
    }

    private Element newConstraintElement()
    {
        final Element result = document.createElement(XMLConst.NODE_CONSTRAINT);

        final String versionText = String.format("%d.%d", XMLFormatVersion.MAJOR, XMLFormatVersion.MINOR); 
        result.setAttribute(XMLConst.ATTR_FORMAT_VERSION, versionText);

        return result;
    }

    private Element newTextBasedElement(String name, String text)
    {
        final Element result = document.createElement(name);
        result.appendChild(document.createTextNode(text));
        return result;
    }
    
    private Element newSignatureElement()
    {
        final Element result = document.createElement(XMLConst.NODE_SIGNATURE);

        for (Variable variable : constraint.getVariables())
            result.appendChild(newVariableElement(variable.getName(), variable.getData()));

        return result;
    }
    
    private Element newVariableElement(String name, Data data)
    {
        final Element result = document.createElement(XMLConst.NODE_VARIABLE);

        result.setAttribute(XMLConst.ATTR_VARIABLE_NAME, name);
        result.setAttribute(XMLConst.ATTR_TYPE_ID, data.getType().getTypeId().toString());
        result.setAttribute(XMLConst.ATTR_DATA_LENGTH, String.valueOf(data.getType().getSize()));
        result.setAttribute(XMLConst.ATTR_VALUE, data.hasValue() ? data.getValue().toString() : "");

        return result;
    }
}

/**
 * The XMLBuilderForExprs class provides functionality for translating an expression tree to a XML tree. 
 * 
 * @author Andrei Tatarnikov
 */

class XMLBuilderForExprs implements Visitor
{
    private final Document       document;
    private final Deque<Element> elements;

    /**
     * Constructs a builder object that will add needed nodes to the specified document. 
     *
     * @param document The document to be built. 
     * @param root The root element of the document to be built.
     */

    public XMLBuilderForExprs(Document document, Element root)
    {
        if (null == document)
            throw new NullPointerException();
        
        if (null == root)
            throw new NullPointerException();
        
        this.document  = document;
        this.elements  = new LinkedList<Element>();
        
        this.elements.addLast(root);
    }

    @Override
    public void onRootBegin()
    {
        assert !elements.isEmpty();

        final Element formula = document.createElement(XMLConst.NODE_FORMULA);
        elements.getLast().appendChild(formula);
        elements.addLast(formula);
    }

    @Override
    public void onRootEnd()
    {
        assert !elements.isEmpty();

        elements.removeLast();
    }

    @Override
    public void onExprBegin(NodeExpr expr)
    {
        final Enum<?> op = expr.getOperationId();

        assert !elements.isEmpty();

        final Element expression = document.createElement(XMLConst.NODE_EXPRESSION);
        elements.getLast().appendChild(expression);
        elements.addLast(expression);
        
        final Element operation = document.createElement(XMLConst.NODE_OPERATION);
        expression.appendChild(operation);

        operation.setAttribute(XMLConst.ATTR_OPERATION_ID, op.name());
        operation.setAttribute(XMLConst.ATTR_OPERATION_FAMILY, op.getClass().getName());
    }

    @Override
    public void onExprEnd(NodeExpr expr)
    {
        assert !elements.isEmpty();

        elements.removeLast();
    }

    @Override
    public void onOperandBegin(NodeExpr expr, Node node, int index)
    {
        // Do nothing.
    }

    @Override
    public void onOperandEnd(NodeExpr expr, Node node, int index)
    {
        // Do nothing.
    }

    @Override
    public void onValue(NodeValue value)
    {
        final Data data = value.getData();
        
        assert !elements.isEmpty();

        final Element valueElement = document.createElement(XMLConst.NODE_VALUE);
        elements.getLast().appendChild(valueElement);

        valueElement.setAttribute(XMLConst.ATTR_TYPE_ID, data.getType().getTypeId().toString());
        valueElement.setAttribute(XMLConst.ATTR_DATA_LENGTH, Integer.toString(data.getType().getSize()));
        valueElement.setAttribute(XMLConst.ATTR_VALUE, data.getValue().toString());
    }

    @Override
    public void onVariable(NodeVariable variable)
    {
        assert !elements.isEmpty();

        final Element variableRef = document.createElement(XMLConst.NODE_VARIABLE_REF);
        elements.getLast().appendChild(variableRef);

        variableRef.setAttribute(XMLConst.ATTR_VARIABLE_NAME, variable.getName());
    }
}