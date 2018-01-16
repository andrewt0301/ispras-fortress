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

/**
 * The XMLFormatVersion class stores information about the current version of the storage format.
 * 
 * @author Andrei Tatarnikov
 */

class XMLFormatVersion {
  private XMLFormatVersion() {}

  public static final int MAJOR = 1;
  public static final int MINOR = 0;
}


/**
 * The XMLConst class stores string constants related to an XML representation of a constraint.
 * 
 * @author Andrei Tatarnikov
 */

class XMLConst {
  private XMLConst() {}

  public static final String NODE_CONSTRAINT = "Constraint";
  public static final String NODE_NAME = "Name";
  public static final String NODE_KIND = "Kind";
  public static final String NODE_DESCRIPTION = "Description";
  public static final String NODE_INNER_REP = "InnerRep";
  public static final String NODE_FORMULA = "Formula";
  public static final String NODE_OPERATION = "Operation";
  public static final String NODE_VARIABLE = "Variable";
  public static final String NODE_VARIABLE_REF = "VariableRef";
  public static final String NODE_VALUE = "Value";
  public static final String NODE_SIGNATURE = "Signature";
  public static final String NODE_BINDING = "Binding";
  public static final String NODE_BINDING_LIST = "BindingList";
  public static final String NODE_BOUND_VARIABLE = "BoundVariable";

  public static final String ATTR_FORMAT_VERSION = "version";
  public static final String ATTR_OPERATION_ID = "id";
  public static final String ATTR_VARIABLE_NAME = "name";
  public static final String ATTR_TYPE_ID = "type";
  public static final String ATTR_VALUE = "value";
  public static final String ATTR_DATA_LENGTH = "length";
  public static final String ATTR_OPERATION_FAMILY = "family";
}


/**
 * The Messages class stores string constants used in exceptions.
 * 
 * @author Andrei Tatarnikov
 */

class Messages {
  private Messages() {}

  public static final String ERR_XML_UNKNOWN_NODE =
      "The \"%s\" node is unexpected in the document.";
  public static final String ERR_XML_NO_ATTRIBUTE =
      "The \"%s\" attribute is not found (the \"%s\" node).";
  public static final String ERR_XML_BAD_ATTIBUTE =
      "The \"%s\" attribute has an invalid value %s (the \"%s\" node).";
  public static final String ERR_XML_BAD_VERSION =
      "Wrong format version. It is %d.%d while %d.%d is expected.";
  public static final String ERR_XML_BAD_HIERARCHY =
      "Wrong node hierarchy. The \"%s\" node cannot be a child of " + "the \"%s\" node.";

  public static final String ERR_INVALID_CONSTRAINT = "Invalid constraint. ";
  public static final String ERR_BAD_CONSTRAINT_KIND = "Unsupported constraint kind: ";
  public static final String ERR_NO_CONSTRAINT_NAME = "The constraint name is not specified.";
  public static final String ERR_NO_CONSTRAINT_KIND = "The constraint kind is not specified.";
  public static final String ERR_ALREADY_STARTED = "Building %s has already been started.";
  public static final String ERR_NO_OPERATION = "No operation has been started.";
  public static final String ERR_NO_EXPRESSION_FOR_OP =
      "No expression is created for the %s operation.";
  public static final String ERR_FORMULA_ALREADY_ASSIGNED = "The formula is already assigned.";

  public static final String ERR_NO_OPERATION_ID = "The operation type is not specified.";
  public static final String ERR_EXTRA_OPERATION_ID = "The operation type is already set.";

  public static final String ERR_UNDEFINED_VARIABLE =
      "The \"%s\" variable cannot be appended to the expression. "
          + "It is absent from the variable definition list.";
}
