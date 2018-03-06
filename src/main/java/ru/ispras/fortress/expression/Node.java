/*
 * Copyright 2013-2018 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.expression;

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.DataTypeId;
import ru.ispras.fortress.jaxb.JaxbNode;
import ru.ispras.fortress.jaxb.JaxbNodeAdapter;
import ru.ispras.fortress.util.InvariantChecks;

import javax.xml.bind.annotation.XmlSeeAlso;
import javax.xml.bind.annotation.adapters.XmlJavaTypeAdapter;

/**
 * The {@link Node} class is a base class for all kinds of classes describing nodes in an expression
 * tree. It includes declarations and implementations of methods common for all node kinds.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
@XmlSeeAlso(JaxbNode.class)
@XmlJavaTypeAdapter(JaxbNodeAdapter.class)
public abstract class Node {
  /**
   * The {@link Node.Kind} enumeration specifies the kind of an expression tree node.
   *
   * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
   */
  public static enum Kind {
    /**
     * A value node. Stores a constant value.
     */
    VALUE,

    /**
     * A variable node. Can be either an unknown variable or a named constant.
     */
    VARIABLE,

    /**
     * An operation node. Describes an expression that includes an operation and one or two
     * operands.
     */
    OPERATION,

    /**
     * A binding node. Represents group of variable substitutions.
     */
    BINDING
  }

  private final Kind kind;
  private Object userData;

  /**
   * Creates a node of the specified kind.
   *
   * @param kind Node kind identifier.
   * @throws IllegalArgumentException if the parameter equals {@code null}.
   */
  protected Node(final Kind kind) {
    InvariantChecks.checkNotNull(kind);
    this.kind = kind;
  }

  /**
   * Constructor for making copies. The fields are copied by reference because the kind field is
   * immutable and the userData field is of an unknown type (there is no way to know how to clone
   * it).
   *
   * @param node Node object to be copied.
   * @throws IllegalArgumentException if the parameter equals {@code null}.
   */
  protected Node(final Node node) {
    InvariantChecks.checkNotNull(node);
    this.kind = node.kind;
    this.userData = node.userData;
  }

  /**
   * Creates a deep copy of the current object referencing user data. All
   * aggregated objects that are not readonly must be cloned.
   *
   * @return Full copy of the current node object.
   */
  public Node deepestCopy() {
    final Node node = deepCopy();
    node.setUserData(getUserData());
    return node;
  }

  /**
   * Creates a deep copy of the current objects. All aggregated objects that are not readonly must
   * be cloned. This excludes user data as its type is unknown.
   *
   * @return Full copy of the current node object.
   */
  public abstract Node deepCopy();

  /**
   * Returns the identifier that specifies the kind of the node.
   *
   * @return A node kind identifier.
   */
  public final Kind getKind() {
    return kind;
  }

  /**
   * Returns an object that describes the type of the value referred by the node.
   *
   * @return A data type object.
   */
  public abstract DataType getDataType();

  /**
   * Returns a data type identifier describing the type of the value referred by the node.
   *
   * @return Data type identifier.
   */
  public final DataTypeId getDataTypeId() {
    return getDataType().getTypeId();
  }

  /**
   * Checks whether the expression has the specified type
   * (types are compared on the {@link DataTypeId} level).
   *
   * @param typeId {@link DataTypeId} object the data type is to be compared to.
   * @return {@code true} if the expression type matches the type specified by
   *         the {@code typeId} argument or {@code false} otherwise.
   */
  public final boolean isType(final DataTypeId typeId) {
    return getDataTypeId() == typeId;
  }

  /**
   * Checks whether the expression has one of the specified types
   * (types are compared on the {@link DataTypeId} level).
   *
   * @param  typeIds List of type identifiers ({@link DataTypeId} objects) the expression type
   *         is to be compared to.
   * @return {@code true} if the expression type matches one of the type identifiers specified
   *         by the {@code typeIds} argument or {@code false} otherwise.
   * @throws IllegalArgumentException if the type identifier collection is empty.
   */
  public final boolean isType(final DataTypeId... typeIds) {
    InvariantChecks.checkNotEmpty(typeIds);
    for (final DataTypeId typeId : typeIds) {
      if (isType(typeId)) {
        return true;
      }
    }
    return false;
  }

  /**
   * Checks whether the stored value has the specified type
   * (types are compared on the {@link DataType} level).
   *
   * @param type {@link DataType} object the data type is to be compared to.
   * @return {@code true} if the expression type matches the type specified by
   *         the {@code type} argument or {@code false} otherwise.
   */
  public final boolean isType(final DataType type) {
    return getDataType().equals(type);
  }

  /**
   * Checks whether the expression has one of the specified types
   * (types are compared on the {@link DataType} level).
   *
   * @param  types List of types ({@link DataType} objects) the expression type
   *         is to be compared to.
   * @return {@code true} if the expression type matches one of the types specified by
   *         the {@code types} argument or {@code false} otherwise.
   * @throws IllegalArgumentException if the type collection is empty.
   */
  public final boolean isType(final DataType... types) {
    InvariantChecks.checkNotEmpty(types);
    for (final DataType type : types) {
      if (isType(type)) {
        return true;
      }
    }
    return false;
  }

  /**
   * Associates a user data object with the current node
   *
   * @param obj User data object.
   */
  public final void setUserData(final Object obj) {
    this.userData = obj;
  }

  /**
   * Returns user data.
   *
   * @return User data object.
   */
  public final Object getUserData() {
    return userData;
  }
}
