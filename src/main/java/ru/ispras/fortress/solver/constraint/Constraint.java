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

package ru.ispras.fortress.solver.constraint;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.util.InvariantChecks;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;

/**
 * The {@link Constraint} class stores a description of a constraint and provides facilities to
 * perform manipulations with it. The Constraint class allows describing various constraint types.
 * Depending on the constraint type (described by the kind field), its internal representation
 * (see the representation field) can use a different class to store the information.
 *
 * @author <a href="mailto:smolov@ispras.ru">Sergey Smolov</a>
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public final class Constraint {
  private final String name;
  private final ConstraintKind kind;
  private final String description;
  private final Map<String, Variable> variables;
  private final Object representation;

  /**
   * Constructs a Constraint object.
   *
   * @param name Constraint name (uniquely identifies the constraint).
   * @param kind Constraint type (gives information about its internal representation format).
   * @param description Constraint description.
   * @param variables Table of constraint variables.
   * @param representation Description of the constraint internals (internal representation) in a
   *        format that depends on the type of the constraint.
   *
   * @throws IllegalArgumentException if any of the parameters equals null.
   * @throws IllegalArgumentException if the internal representation class does not match the class
   *         required by the constraint type.
   */
  public Constraint(
      final String name,
      final ConstraintKind kind,
      final String description,
      final Map<String, Variable> variables,
      final Object representation) {
    InvariantChecks.checkNotNull(name);
    InvariantChecks.checkNotNull(kind);
    InvariantChecks.checkNotNull(description);
    InvariantChecks.checkNotNull(variables);
    InvariantChecks.checkNotNull(representation);

    if (representation.getClass() != kind.getInnerRepClass()) {
      throw new IllegalArgumentException(String.format(ILLEGAL_IR_CLASS,
        representation.getClass().getName(), kind.getInnerRepClass().getName()));
    }

    this.name = name;
    this.description = description;
    this.kind = kind;
    this.variables = variables;
    this.representation = representation;
  }

  /**
   * Returns the name that uniquely identifies a constraint.
   *
   * @return Name identifier for the constraint
   */
  public String getName() {
    return name;
  }

  /**
   * Returns information on the constraint type (including the format of its internals).
   *
   * @return Constraint type information.
   */
  public ConstraintKind getKind() {
    return kind;
  }

  /**
   * Returns the description of the constraint (some additional information).
   *
   * @return Textual description of the constraint.
   */
  public String getDescription() {
    return description;
  }

  /**
   * Returns an object that holds internal description of the constraint. The exact type of the
   * object depends on the constraint type.
   *
   * @return Internal representation of the constraint.
   */
  public Object getInnerRep() {
    return representation;
  }

  /**
   * Assigns a value to a constraint variable (makes it an input variable).
   *
   * @param name The name of the variable.
   * @param value The data object that stores the variable value.
   *
   * @throws IllegalArgumentException if any of the parameters equals null.
   * @throws IllegalArgumentException (1) if a variable with such name is not defined; (2) if the
   *         value type does not match the type of the variable.
   */
  public void setVariableValue(final String name, final Data value) {
    InvariantChecks.checkNotNull(name);
    InvariantChecks.checkNotNull(value);

    if (!variables.containsKey(name)) {
      throw new IllegalArgumentException(String.format(UNDEFINED_VARIABLE, name));
    }

    final Variable variable = variables.get(name);
    if (!variable.getData().getType().equals(value.getType())) {
      throw new IllegalArgumentException(String.format(ILLEGAL_TYPE,
        variable.getData().getType(), value.getType()));
    }

    variable.setData(value);
  }

  /**
   * Finds a constraint variable by its name. If no such variable is found, null is returned.
   *
   * @param name The name of the variable to be searched for.
   * @return variable Variable object or null if the variable is not defined.
   *
   * @throws IllegalArgumentException if the name parameter equals null.
   */
  public Variable findVariable(final String name) {
    InvariantChecks.checkNotNull(name);
    return variables.get(name);
  }

  /**
   * Returns a collection of constraint variables.
   *
   * @return variables A collection of constraint variables.
   */
  public Collection<Variable> getVariables() {
    return Collections.unmodifiableCollection(variables.values());
  }

  /**
   * Returns a collection of unknown constraint variables (that have no assigned value).
   *
   * @return A collection of constraint variables.
   */
  public Collection<Variable> getUnknownVariables() {
    final List<Variable> result = new ArrayList<Variable>(variables.size());

    for (final Variable variable : variables.values()) {
      if (!variable.hasValue()) {
        result.add(variable);
      }
    }

    return result;
  }

  @Override
  public int hashCode() {
    final int prime = 31;
    int result = 1;

    result = prime * result + name.hashCode();
    result = prime * result + kind.hashCode();
    result = prime * result + variables.hashCode();
    result = prime * result + representation.hashCode();

    return result;
  }

  @Override
  public boolean equals(final Object obj) {
    if (this == obj) {
      return true;
    }

    if (obj == null) {
      return false;
    }

    if (getClass() != obj.getClass()) {
      return false;
    }

    final Constraint other = (Constraint) obj;
    if (!name.equals(other.name)) {
      return false;
    }

    if (kind != other.kind) {
      return false;
    }

    if (!variables.equals(other.variables)) {
      return false;
    }

    if (null == representation) {
      return representation == other.representation;
    }

    return representation.equals(other.representation);
  }

  @Override
  public String toString() {
    return representation.toString();
  }

  private static final String UNDEFINED_VARIABLE =
      "%s is illegal variable name. No such varaible is defined.";

  private static final String ILLEGAL_TYPE =
      "%s is illegal data type, %s is expected.";

  private static final String ILLEGAL_IR_CLASS =
      "%s is illegal representation class, %s is expected.";
}
