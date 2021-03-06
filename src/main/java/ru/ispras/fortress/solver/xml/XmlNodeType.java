/*
 * Copyright 2012-2018 ISP RAS (http://www.ispras.ru)
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

import java.util.EnumSet;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

/**
 * The {@link XmlNodeType} enumeration describes XML nodes that correspond to attributes of
 * a constraint. It is used in the logic that parses an XML document to build a constraint and
 * checks its correctness.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
enum XmlNodeType {
  /**
   * The root node of the document. Contains all information describing a constraint. Specifies the
   * current format version as an attribute. Contains child nodes.
   */
  CONSTRAINT(XmlConst.NODE_CONSTRAINT),

  /**
   * Specifies the name of a constraint. A child of the Constraint node. Contains text.
   */
  NAME(XmlConst.NODE_NAME),

  /**
   * Stores information about the constraint. A child of the Constraint node. Contains text.
   */
  KIND(XmlConst.NODE_KIND),

  /**
   * Stores the description of a constraint. A child of the Constraint node. Contains text.
   */
  DESCRIPTION(XmlConst.NODE_DESCRIPTION),

  /**
   * The root node for a tree describing the internal representation of a constraint. For example,
   * it can contain a list of formula expressions that should be satisfied.
   */
  INNER_REP(XmlConst.NODE_INNER_REP),

  /**
   * Specifies a logic formula (or an assertion) describing a condition the constraint must satisfy.
   */
  FORMULA(XmlConst.NODE_FORMULA),

  /**
   * Specifies the operation performed by operands of an expression.
   */
  OPERATION(XmlConst.NODE_OPERATION),

  /**
   * Specifies a reference to a global variable which is used in an expression as an operand.
   */
  VARIABLE_REF(XmlConst.NODE_VARIABLE_REF),

  /**
   * Specifies a value used in an expression as an operand.
   */
  VALUE(XmlConst.NODE_VALUE),

  /**
   * Describes the signature of a constraint including global variables.
   */
  SIGNATURE(XmlConst.NODE_SIGNATURE),

  /**
   * Specifies a global variable.
   */
  VARIABLE(XmlConst.NODE_VARIABLE),

  /**
   * Specifies an expression with bound variables.
   */
  BINDING(XmlConst.NODE_BINDING),

  /**
   * Specifies a list of bound variables.
   */
  BINDING_LIST(XmlConst.NODE_BINDING_LIST),

  /**
   * Specifies a local variable is to be replaced in expression.
   */
  BOUND_VARIABLE(XmlConst.NODE_BOUND_VARIABLE);

  private static final Map<String, XmlNodeType> NAME_TO_TYPE_MAP;
  static {
    final Set<XmlNodeType> constraintSet = EnumSet.of(CONSTRAINT);
    final Set<XmlNodeType> nestingSet = EnumSet.of(FORMULA, OPERATION, BINDING, BOUND_VARIABLE);

    CONSTRAINT.parents = EnumSet.noneOf(XmlNodeType.class);
    NAME.parents = constraintSet;
    KIND.parents = constraintSet;
    DESCRIPTION.parents = constraintSet;
    INNER_REP.parents = constraintSet;
    FORMULA.parents = EnumSet.of(INNER_REP);
    OPERATION.parents = nestingSet;
    VARIABLE_REF.parents = EnumSet.of(OPERATION, FORMULA);
    VALUE.parents = nestingSet;
    SIGNATURE.parents = constraintSet;
    VARIABLE.parents = EnumSet.of(SIGNATURE);
    BINDING.parents = nestingSet;
    BINDING_LIST.parents = EnumSet.of(BINDING);
    BOUND_VARIABLE.parents = EnumSet.of(BINDING_LIST);

    NAME_TO_TYPE_MAP = new HashMap<>();
    for (final XmlNodeType type : values()) {
      if (null == type.parents) {
        throw new IllegalStateException(String.format(
          "%s.parents is not initialized.", type.name()));
      }

      NAME_TO_TYPE_MAP.put(type.getNodeName(), type);
    }
  }

  private final String nodeName;
  private Set<XmlNodeType> parents;

  private XmlNodeType(final String nodeName) {
    this.nodeName = nodeName;
    this.parents = null;
  }

  String getNodeName() {
    return nodeName;
  }

  boolean isChildOf(final XmlNodeType parent) {
    if ((null == parent) && parents.isEmpty()) {
      return true;
    }

    return parents.contains(parent);
  }

  static XmlNodeType fromNodeName(final String name) {
    return NAME_TO_TYPE_MAP.get(name);
  }
}
