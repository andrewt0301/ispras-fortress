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
