/*
 * Copyright 2012-2014 ISP RAS (http://www.ispras.ru)
 * 
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 * 
 * http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software distributed under the License
 * is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
 * or implied. See the License for the specific language governing permissions and limitations under
 * the License.
 */

package ru.ispras.fortress.solver.xml;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.OutputStream;
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
import ru.ispras.fortress.expression.ExprTreeVisitor;
import ru.ispras.fortress.expression.ExprTreeWalker;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeBinding;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintKind;
import ru.ispras.fortress.solver.constraint.Formulas;
import ru.ispras.fortress.util.InvariantChecks;

/**
 * The XMLConstraintSaver class provides functionality to save a constraint with all its attributes
 * to an XML file.
 * 
 * @author Andrei Tatarnikov
 */

public final class XMLConstraintSaver {
  private final Constraint constraint;
  private Document document;

  /**
   * Constructs an XMLConstraintSaver object that saves the specified constraint to the specified
   * XML document.
   * 
   * @param constraint Constraint to be save.
   * 
   * @throws NullPointerException if the parameter equals null.
   * @throws IllegalArgumentException if the constraint is not formula-based (its type is not
   *         FORMULA_BASED). Currently, the possibility of saving other constraint types is not
   *         implemented.
   */

  public XMLConstraintSaver(final Constraint constraint) {
    InvariantChecks.checkNotNull(constraint);

    if (ConstraintKind.FORMULA_BASED != constraint.getKind()) {
      throw new IllegalArgumentException(Messages.ERR_BAD_CONSTRAINT_KIND + constraint.getKind());
    }

    this.constraint = constraint;
    this.document = null;
  }

  /**
   * Saves the constraint object to an XML string.
   * 
   * @return XML text for the constraint.
   * @throws XMLNotSavedException if failed to save the constraint to a string.
   */

  public String saveToString() throws XMLNotSavedException {
    try {
      document = newDocument();
      buildDocument();
      return saveDocumentToString(document);
    } catch (Exception e) {
      throw new XMLNotSavedException(e);
    } finally {
      document = null;
    }
  }

  /**
   * Saves the constraint object to an XML file.
   * 
   * @param fileName Target XML document file name.
   * 
   * @throws NullPointerException if the parameter equals null.
   * @throws XMLNotSavedException if failed to save the constraint to a file.
   */

  public void saveToFile(final String fileName) throws XMLNotSavedException {
    InvariantChecks.checkNotNull(fileName);

    try {
      document = newDocument();
      buildDocument();

      saveDocumentToFile(document, fileName);
    } catch (Exception e) {
      throw new XMLNotSavedException(fileName, e);
    } finally {
      document = null;
    }
  }

  private void buildDocument() {
    final Element root = newConstraintElement();
    document.appendChild(root);

    root.appendChild(newTextBasedElement(XMLConst.NODE_NAME, constraint.getName()));
    root.appendChild(newTextBasedElement(XMLConst.NODE_KIND, constraint.getKind().name()));
    root.appendChild(newTextBasedElement(XMLConst.NODE_DESCRIPTION, constraint.getDescription()));
    root.appendChild(newSignatureElement());

    final Element innerRep = document.createElement(XMLConst.NODE_INNER_REP);
    root.appendChild(innerRep);

    final ExprTreeWalker walker = new ExprTreeWalker(new XMLBuilderForExprs(document, innerRep));

    walker.visit(((Formulas) constraint.getInnerRep()).exprs());
  }

  private static Document newDocument() throws ParserConfigurationException {
    final DocumentBuilderFactory docFactory = DocumentBuilderFactory.newInstance();
    final DocumentBuilder docBuilder = docFactory.newDocumentBuilder();

    return docBuilder.newDocument();
  }

  private static void saveDocumentToFile(final Document document, final String fileName)
      throws TransformerConfigurationException, TransformerException {
    final DOMSource source = new DOMSource(document);
    final StreamResult streamResult = new StreamResult(new File(fileName));

    newTransformer().transform(source, streamResult);
  }

  private static String saveDocumentToString(final Document document)
      throws TransformerConfigurationException, TransformerException {
    final DOMSource source = new DOMSource(document);
    final OutputStream os = new ByteArrayOutputStream();
    final StreamResult streamResult = new StreamResult(os);

    newTransformer().transform(source, streamResult);
    return os.toString();
  }

  private static Transformer newTransformer() throws TransformerConfigurationException {
    final TransformerFactory transformerFactory = TransformerFactory.newInstance();
    final Transformer transformer = transformerFactory.newTransformer();

    transformer.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "no");
    transformer.setOutputProperty(OutputKeys.METHOD, "xml");
    transformer.setOutputProperty(OutputKeys.INDENT, "yes");
    transformer.setOutputProperty(OutputKeys.ENCODING, "UTF-8");
    transformer.setOutputProperty("{http://xml.apache.org/xslt}indent-amount", "4");

    return transformer;
  }

  private Element newConstraintElement() {
    final Element result = document.createElement(XMLConst.NODE_CONSTRAINT);

    final String versionText = String.format("%d.%d",
        XMLFormatVersion.MAJOR, XMLFormatVersion.MINOR);

    result.setAttribute(XMLConst.ATTR_FORMAT_VERSION, versionText);
    return result;
  }

  private Element newTextBasedElement(final String name, final String text) {
    final Element result = document.createElement(name);
    result.appendChild(document.createTextNode(text));
    return result;
  }

  private Element newSignatureElement() {
    final Element result = document.createElement(XMLConst.NODE_SIGNATURE);

    for (final Variable variable : constraint.getVariables()) {
      result.appendChild(newVariableElement(variable.getName(), variable.getData()));
    }

    return result;
  }

  private Element newVariableElement(final String name, final Data data) {
    final Element result = document.createElement(XMLConst.NODE_VARIABLE);

    result.setAttribute(XMLConst.ATTR_VARIABLE_NAME, name);
    result.setAttribute(XMLConst.ATTR_TYPE_ID, data.getType().toString());
    result.setAttribute(XMLConst.ATTR_VALUE, data.hasValue() ? data.getValue().toString() : "");

    return result;
  }
}


/**
 * The XMLBuilderForExprs class provides functionality for translating an expression tree to a XML
 * tree.
 * 
 * @author Andrei Tatarnikov
 */

class XMLBuilderForExprs implements ExprTreeVisitor {
  private final Document document;
  private final Deque<Element> elements;

  /**
   * Constructs a builder object that will add needed nodes to the specified document.
   * 
   * @param document The document to be built.
   * @param root The root element of the document to be built.
   */

  public XMLBuilderForExprs(final Document document, final Element root) {
    InvariantChecks.checkNotNull(document);
    InvariantChecks.checkNotNull(root);

    this.document = document;
    this.elements = new LinkedList<Element>();

    this.elements.addLast(root);
  }

  @Override
  public Status getStatus() {
    // We are not going to stop the walker or to skip any subtrees.
    // Therefore, it is always OK.
    return Status.OK;
  }

  @Override
  public void onRootBegin() {
    assert !elements.isEmpty();

    final Element formula = document.createElement(XMLConst.NODE_FORMULA);
    elements.getLast().appendChild(formula);
    elements.addLast(formula);
  }

  @Override
  public void onRootEnd() {
    assert !elements.isEmpty();

    elements.removeLast();
  }

  @Override
  public void onOperationBegin(final NodeOperation expr) {
    final Enum<?> op = expr.getOperationId();

    assert !elements.isEmpty();

    final Element operation = document.createElement(XMLConst.NODE_OPERATION);
    elements.getLast().appendChild(operation);
    elements.addLast(operation);

    operation.setAttribute(XMLConst.ATTR_OPERATION_ID, op.name());
    operation.setAttribute(XMLConst.ATTR_OPERATION_FAMILY, op.getClass().getName());
  }

  @Override
  public void onOperationEnd(final NodeOperation expr) {
    assert !elements.isEmpty();

    elements.removeLast();
  }

  @Override
  public int[] getOperandOrder() {
    return null;
  }

  @Override
  public void onOperandBegin(
      final NodeOperation expr,
      final Node node,
      final int index) {
    // Do nothing.
  }

  @Override
  public void onOperandEnd(
      final NodeOperation expr,
      final Node node,
      final int index) {
    // Do nothing.
  }

  @Override
  public void onValue(final NodeValue value) {
    final Data data = value.getData();

    assert !elements.isEmpty();

    final Element valueElement = document.createElement(XMLConst.NODE_VALUE);
    elements.getLast().appendChild(valueElement);

    valueElement.setAttribute(XMLConst.ATTR_TYPE_ID, data.getType().toString());
    valueElement.setAttribute(XMLConst.ATTR_VALUE, data.getValue().toString());
  }

  @Override
  public void onVariable(final NodeVariable variable) {
    assert !elements.isEmpty();

    final Element variableRef = document.createElement(XMLConst.NODE_VARIABLE_REF);
    elements.getLast().appendChild(variableRef);

    variableRef.setAttribute(XMLConst.ATTR_VARIABLE_NAME, variable.getName());
  }

  @Override
  public void onBindingBegin(final NodeBinding node) {
    assert !elements.isEmpty();

    final Element binding = document.createElement(XMLConst.NODE_BINDING);
    final Element bindingList = document.createElement(XMLConst.NODE_BINDING_LIST);

    binding.appendChild(bindingList);
    elements.getLast().appendChild(binding);

    elements.addLast(binding);
    elements.addLast(bindingList);
  }

  @Override
  public void onBindingListEnd(final NodeBinding node) {
    assert !elements.isEmpty();
    elements.removeLast();
  }

  @Override
  public void onBindingEnd(final NodeBinding node) {
    assert !elements.isEmpty();
    elements.removeLast();
  }

  @Override
  public void onBoundVariableBegin(
      final NodeBinding node,
      final NodeVariable variable,
      final Node value) {
    assert !elements.isEmpty();

    final Element binding = document.createElement(XMLConst.NODE_BOUND_VARIABLE);
    elements.getLast().appendChild(binding);
    elements.addLast(binding);

    binding.setAttribute(XMLConst.ATTR_VARIABLE_NAME, variable.getName());
  }

  @Override
  public void onBoundVariableEnd(
      final NodeBinding node,
      final NodeVariable variable,
      final Node value) {
    assert !elements.isEmpty();
    elements.removeLast();
  }
}
