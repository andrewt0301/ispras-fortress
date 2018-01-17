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
 * The {@link XmlMessages} class stores string constants used in exceptions.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
final class XmlMessages {
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