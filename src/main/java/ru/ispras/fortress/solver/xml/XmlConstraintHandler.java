/*
 * Copyright 2014-2018 ISP RAS (http://www.ispras.ru)
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

import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeBinding;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintBuilder;
import ru.ispras.fortress.solver.constraint.ConstraintKind;
import ru.ispras.fortress.solver.constraint.Formulas;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;

/**
 * The {@link XmlConstraintHandler} class is handler for SAX parser events that builds a constraint
 * basing on its XML representation.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
final class XmlConstraintHandler extends DefaultHandler {

  private final XmlConstraintBuilder builder = new XmlConstraintBuilder();
  private final Stack<XmlNodeType> nodes = new Stack<>();
  private final Map<String, Variable> variables = new HashMap<>();

  private final Map<String, Variable> incompleteScope = new HashMap<>();
  private VariableScope nestedScope = VariableScope.EMPTY_SCOPE;

  public Constraint getConstraint() {
    return builder.getConstraint();
  }

  @Override
  public void startElement(
      final String uri,
      final String localName,
      final String qualifiedName,
      final Attributes attributes) throws SAXException {
    try {
      final XmlNodeType currentNode = getNodeType(qualifiedName);
      verifyNodeHierarchy(currentNode, nodes.empty() ? null : nodes.lastElement());

      switch (currentNode) {
        case CONSTRAINT: {
          nodes.clear();
          verifyFormatVersion(qualifiedName, attributes);
          builder.beginConstraint();
          break;
        }

        case INNER_REP: {
          builder.beginInnerRep();
          break;
        }

        case FORMULA: {
          builder.beginFormula();
          break;
        }

        case OPERATION: {
          builder.beginOperation();
          builder.pushOperation(getOperationId(qualifiedName, attributes));
          break;
        }

        case VARIABLE_REF: {
          final String variableName = getVariableRef(qualifiedName, attributes);

          if (nestedScope.contains(variableName)) {
            builder.pushElement(new NodeVariable(nestedScope.get(variableName)));
          } else if (variables.containsKey(variableName)) {
            builder.pushElement(new NodeVariable(variables.get(variableName)));
          } else {
            throw new SAXException(String.format(XmlMessages.ERR_UNDEFINED_VARIABLE, variableName));
          }

          break;
        }

        case VALUE: {
          final Data value = getValue(qualifiedName, attributes);
          builder.pushElement(new NodeValue(value));
          break;
        }

        case SIGNATURE: {
          builder.beginSignature();
          break;
        }

        case VARIABLE: {
          final Variable variable =
              builder.addGlobalVariable(getVariable(qualifiedName, attributes));
          variables.put(variable.getName(), variable);
          break;
        }

        case BINDING: {
          builder.beginBinding();
          break;
        }

        case BOUND_VARIABLE: {
          final String variableName = getVariableRef(qualifiedName, attributes);
          final Variable variable = createLocalVariable(variableName);

          incompleteScope.put(variableName, variable);
          builder.pushElement(new NodeVariable(variable));

          break;
        }

        case BINDING_LIST:
        case NAME:
        case KIND:
        case DESCRIPTION: {
          // Do nothing
          break;
        }

        default: {
          assert false;
          break;
        }
      }

      nodes.push(currentNode);
    } catch (final SAXException e) {
      throw e;
    } catch (final Exception e) {
      throw new SAXException(XmlMessages.ERR_INVALID_CONSTRAINT + e.getMessage(), e);
    }

    // ///////// DEBUG CODE ////////////////////////
    // System.out.print("<" + qualifiedName + ">");
    // for (int index = 0; index < attributes.getLength(); ++index)
    // {
    // System.out.print(" " + attributes.getLocalName(index) +
    // "=\"" + attributes.getValue(index) + "\" ");
    // }
  }

  private Variable createLocalVariable(final String name) {
    return new Variable(name, DataType.UNKNOWN);
  }

  @Override
  public void endElement(
      final String uri,
      final String localName,
      final String qualifiedName) throws SAXException {
    assert !nodes.empty();
    try {
      final XmlNodeType currentNode = getNodeType(qualifiedName);
      assert (currentNode == nodes.lastElement());

      switch (currentNode) {
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
    } catch (final SAXException e) {
      throw e;
    } catch (final Exception e) {
      throw new SAXException(XmlMessages.ERR_INVALID_CONSTRAINT + e.getMessage(), e);
    }

    // ///////// DEBUG CODE ////////////////////////
    // System.out.print("</" + qualifiedName + ">");
  }

  private void pushVariableScope() {
    nestedScope = new VariableScope(nestedScope, new HashMap<String, Variable>(incompleteScope));
    incompleteScope.clear();
  }

  private void popVariableScope() {
    nestedScope = nestedScope.getHiddenScope();
  }

  @Override
  public void characters(
      final char[] ch, final int start, final int length) throws SAXException {
    assert !nodes.empty();

    switch (nodes.lastElement()) {
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

    // ///////// DEBUG CODE ////////////////////////
    // System.out.print(new String(ch, start, length));
  }

  private static XmlNodeType getNodeType(final String nodeName) throws SAXException {
    final XmlNodeType nodeType = XmlNodeType.fromNodeName(nodeName);

    if (null == nodeType) {
      throw new SAXException(String.format(XmlMessages.ERR_XML_UNKNOWN_NODE, nodeName));
    }

    return nodeType;
  }

  private static String getAttribute(
      final String nodeName,
      final Attributes attributes,
      final String attributeName) throws SAXException {
    final String attribute = attributes.getValue(attributeName);

    if (null == attribute) {
      throw new SAXException(
          String.format(XmlMessages.ERR_XML_NO_ATTRIBUTE, attributeName, nodeName));
    }

    return attribute;
  }

  // XML representation: <Constraint version="1.0">
  private static void verifyFormatVersion(
      final String nodeName, final Attributes attributes) throws SAXException {
    final String versionString = getAttribute(nodeName, attributes, XmlConst.ATTR_FORMAT_VERSION);

    if (!versionString.matches("[\\d]+[.][\\d]+")) {
      throw new SAXException(String.format(XmlMessages.ERR_XML_BAD_ATTIBUTE,
          XmlConst.ATTR_FORMAT_VERSION, versionString, nodeName));
    }

    final int majorVersion = Integer.valueOf(versionString.split("[.]")[0]);
    final int minorVersion = Integer.valueOf(versionString.split("[.]")[1]);

    if ((XmlFormatVersion.MAJOR != majorVersion) || (XmlFormatVersion.MINOR != minorVersion)) {
      throw new SAXException(String.format(XmlMessages.ERR_XML_BAD_VERSION, majorVersion,
          minorVersion, XmlFormatVersion.MAJOR, XmlFormatVersion.MINOR));
    }
  }

  private static void verifyNodeHierarchy(
      final XmlNodeType current,
      final XmlNodeType parent) throws SAXException {
    if (!current.isChildOf(parent)) {
      throw new SAXException(String.format(
          XmlMessages.ERR_XML_BAD_HIERARCHY, current.getNodeName(), parent.getNodeName()));
    }
  }

  // XML representation: <Value type="(BIT_VECTOR 3)" value="11"/>
  private static Data getValue(
      final String nodeName,
      final Attributes attributes) throws SAXException {
    final String typeIdString = getAttribute(nodeName, attributes, XmlConst.ATTR_TYPE_ID);
    final String valueString = getAttribute(nodeName, attributes, XmlConst.ATTR_VALUE);
    final DataType typeInfo = DataType.typeOf(typeIdString);

    return typeInfo.valueOf(valueString, typeInfo.getTypeRadix());
  }

  // XML representation: <Variable name="aaa" type="(BIT_VECTOR 3)" value=""/>
  private static Variable getVariable(
      final String nodeName,
      final Attributes attributes) throws SAXException {
    final String variableName = getAttribute(nodeName, attributes, XmlConst.ATTR_VARIABLE_NAME);
    final String typeIdString = getAttribute(nodeName, attributes, XmlConst.ATTR_TYPE_ID);
    final String valueString = getAttribute(nodeName, attributes, XmlConst.ATTR_VALUE);

    final DataType typeInfo = DataType.typeOf(typeIdString);

    return valueString.isEmpty()
        ? new Variable(variableName, typeInfo)
        : new Variable(variableName, typeInfo.valueOf(valueString, typeInfo.getTypeRadix()));
  }

  // XML representation: <VariableRef name="aaa"/>
  private static String getVariableRef(
      final String nodeName,
      final Attributes attributes) throws SAXException {
    return getAttribute(nodeName, attributes, XmlConst.ATTR_VARIABLE_NAME);
  }

  // XML representation: <Operation id="BVAND"/>
  @SuppressWarnings({"unchecked", "rawtypes"})
  private static Enum<?> getOperationId(
      final String nodeName, final Attributes attributes) throws Exception {
    final String id = getAttribute(nodeName, attributes, XmlConst.ATTR_OPERATION_ID);
    final String family = getAttribute(nodeName, attributes, XmlConst.ATTR_OPERATION_FAMILY);

    final Class<?> idClass = Class.forName(family);
    return Enum.valueOf((Class<Enum>) idClass, id);
  }

  private static class VariableScope {

    public static final VariableScope EMPTY_SCOPE = new VariableScope() {
      @Override
      public boolean contains(final String name) {
        return false;
      }

      @Override
      public Variable get(final String name) {
        return null;
      }
    };

    private final Map<String, Variable> variables;
    private final VariableScope hidden;

    private VariableScope() {
      this.variables = Collections.emptyMap();
      this.hidden = null;
    }

    public VariableScope(
        final VariableScope previous,
        final Map<String, Variable> variables) {
      this.variables = variables;
      this.hidden = previous;
    }

    public VariableScope getHiddenScope() {
      return hidden;
    }

    public boolean contains(final String name) {
      if (variables.containsKey(name)) {
        return true;
      }

      return hidden.contains(name);
    }

    public Variable get(final String name) {
      if (variables.containsKey(name)) {
        return variables.get(name);
      }

      return hidden.get(name);
    }
  }

  /**
   * The {@link XmlConstraintBuilder} class implements functionality that build a constraint.
   *
   * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
   */
  private static final class XmlConstraintBuilder {
    private ConstraintBuilder constraint = null;
    private String name = null;
    private ConstraintKind kind = null;
    private Formulas formulas = null;
    private Node formula = null;

    private final Stack<OperationBuilder> operations = new Stack<>();

    private void cleanup() {
      constraint = null;
      kind = null;
      name = null;

      formulas = null;
      formula = null;

      operations.clear();
    }

    public void beginConstraint() throws Exception {
      cleanup();
      constraint = new ConstraintBuilder();
    }

    public void endConstraint() throws Exception {
      if (null == name) {
        throw new Exception(XmlMessages.ERR_NO_CONSTRAINT_NAME);
      }

      if (null == kind) {
        throw new Exception(XmlMessages.ERR_NO_CONSTRAINT_KIND);
      }
    }

    public void beginSignature() throws Exception {
      //
    }

    public void endSignature() throws Exception {
      //
    }

    public void beginInnerRep() throws Exception {
      if (null != formulas) {
        throw new IllegalStateException(String.format(
            XmlMessages.ERR_ALREADY_STARTED, "InnerRep"));
      }

      formulas = new Formulas();
    }

    public void endInnerRep() throws Exception {
      // Nothing
    }

    public void beginFormula() throws Exception {
      if (null != formula) {
        throw new IllegalStateException(String.format(
            XmlMessages.ERR_ALREADY_STARTED, "Formula"));
      }

      formula = null;
    }

    public void endFormula() throws Exception {
      formulas.add(formula);
      formula = null;
    }

    public void beginOperation() throws Exception {
      operations.push(new OperationBuilder());
    }

    public void endOperation() throws Exception {
      if (operations.empty()) {
        throw new IllegalStateException(XmlMessages.ERR_NO_OPERATION);
      }

      final NodeOperation expr = operations.pop().build();

      if (operations.empty()) {
        if (null != formula) {
          throw new IllegalStateException(XmlMessages.ERR_FORMULA_ALREADY_ASSIGNED);
        }

        formula = expr;
      } else {
        pushElement(expr);
      }
    }

    public void beginBinding() throws Exception {
      operations.push(new OperationBuilder());
    }

    public void endBinding() throws Exception {
      if (operations.empty()) {
        throw new IllegalStateException(XmlMessages.ERR_NO_OPERATION);
      }

      final NodeBinding node = operations.pop().buildBinding();

      if (operations.empty()) {
        if (null != formula) {
          throw new IllegalStateException(XmlMessages.ERR_FORMULA_ALREADY_ASSIGNED);
        }

        formula = node;
      } else {
        pushElement(node);
      }
    }

    public void pushElement(final Node se) throws Exception {
      if (operations.empty()) {
        if (null != formula) {
          throw new IllegalStateException(XmlMessages.ERR_FORMULA_ALREADY_ASSIGNED);
        }

        formula = se;
      } else {
        operations.lastElement().addElement(se);
      }
    }

    public void pushOperation(final Enum<?> oid) throws Exception {
      if (operations.empty()) {
        throw new IllegalStateException(String.format(
            XmlMessages.ERR_NO_EXPRESSION_FOR_OP, oid.name()));
      }

      operations.lastElement().setOperationId(oid);
    }

    public void setName(final String name) {
      this.name = name;
    }

    public void setDescription(final String description) {
      this.constraint.setDescription(description);
    }

    public void setKind(final ConstraintKind kind) {
      this.kind = kind;
    }

    public Variable addGlobalVariable(final Variable variable) {
      return constraint.addVariable(variable.getName(), variable.getData());
    }

    public Constraint getConstraint() {
      constraint.setName(name);
      constraint.setKind(kind);
      constraint.setInnerRep(formulas);
      return constraint.build();
    }
  }

  /**
   * The {@link OperationBuilder} class is aimed to build an operation expression from its
   * attributes (operation and operands).
   *
   * @author Andrei Tatarnikov
   */
  private static final class OperationBuilder {
    private Enum<?> operationId;
    private final List<Node> elements;

    public OperationBuilder() {
      this.operationId = null;
      this.elements = new ArrayList<>();
    }

    public void setOperationId(final Enum<?> operationId) throws Exception {
      if (null != this.operationId) {
        throw new Exception(XmlMessages.ERR_EXTRA_OPERATION_ID);
      }

      this.operationId = operationId;
    }

    public void addElement(final Node node) throws Exception {
      elements.add(node);
    }

    public NodeOperation build() throws Exception {
      if (null == operationId) {
        throw new Exception(XmlMessages.ERR_NO_OPERATION_ID);
      }

      return new NodeOperation(operationId, elements);
    }

    public NodeBinding buildBinding() throws Exception {
      final Node expr = elements.remove(elements.size() - 1);
      final List<NodeBinding.BoundVariable> bindings = new ArrayList<>();

      for (int index = 0; index < elements.size(); index += 2) {
        if (!(elements.get(index) instanceof NodeVariable)) {
          throw new Exception("NodeVariable expected");
        }

        final NodeVariable var = (NodeVariable) elements.get(index);
        bindings.add(NodeBinding.bindVariable(var, elements.get(index + 1)));
      }

      return new NodeBinding(expr, bindings);
    }
  }
}
