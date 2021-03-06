/*
 * Copyright 2012-2017 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.data;

import ru.ispras.fortress.jaxb.JaxbVariableAdapter;
import ru.ispras.fortress.util.InvariantChecks;
import ru.ispras.fortress.util.Value;
import ru.ispras.fortress.util.ValueConst;

import javax.xml.bind.annotation.adapters.XmlJavaTypeAdapter;

/**
 * The {@link Variable} class describes a variable that can be used as input or
 * output data in constraints.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
@XmlJavaTypeAdapter(JaxbVariableAdapter.class)
public final class Variable {
  private final String name;
  private Value<Data> data;

  /**
   * Constructs a variable from its name and associated dynamic data.
   * Used for creating context-dependent variables.
   *
   * @param name Variable name.
   * @param data Dynamic value.
   *
   * @throws IllegalArgumentException if any of the parameters equals {@code null}.
   */
  public Variable(final String name, final Value<Data> data) {
    InvariantChecks.checkNotNull(name);
    InvariantChecks.checkNotNull(data);

    this.name = name;
    this.data = data;
  }

  /**
   * Constructs a variable from its name and associated data.
   *
   * @param name Variable name.
   * @param data Data the variable refers to.
   *
   * @throws IllegalArgumentException if any of the parameters equals {@code null}.
   */
  public Variable(final String name, final Data data) {
    this(name, new ValueConst<>(data));
    InvariantChecks.checkNotNull(data);
  }

  /**
   * Constructs an uninitialized variable of the specified type. The constructed variable does not
   * refer to any data and its value is set to {@code null}.
   *
   * @param name Variable name.
   * @param type Variable type.
   *
   * @throws IllegalArgumentException if any of the parameters equals {@code null}.
   */
  public Variable(final String name, final DataType type) {
    this(name, type != null ? type.valueUninitialized() : null);
  }

  /**
   * Constructs a full copy of the given variable object. The fields are copied by reference
   * because their types are immutable.
   *
   * @param variable Variable object to be copied.
   *
   * @throws IllegalArgumentException if the parameter equals {@code null}.
   */
  public Variable(final Variable variable) {
    this(variable != null ? variable.name : null, variable != null ? variable.data : null);
  }

  /**
   * Assigns a new data value to the variable.
   *
   * @param data A data value to be assigned to the variable.
   *
   * @throws IllegalArgumentException if the parameter equals {@code null}.
   */
  public void setData(final Data data) {
    InvariantChecks.checkNotNull(data);
    this.data = new ValueConst<Data>(data);
  }

  /**
   * Returns the name of the variable.
   *
   * @return A string representing the variable name.
   */
  public String getName() {
    return name;
  }

  /**
   * Returns a data object associated with the specified variable.
   *
   * @return A {@link Data} object associated with the variable.
   */
  public Data getData() {
    return data.value();
  }

  /**
   * Returns the type of the variable.
   *
   * @return Variable type.
   */
  public DataType getType() {
    return getData().getType();
  }

  /**
   * Checks whether the variable has a value assigned to it.
   *
   * @return {@code true} if the variable has a value assigned or {@code false} otherwise.
   */
  public boolean hasValue() {
    return getData().hasValue();
  }

  @Override
  public int hashCode() {
    final int prime = 31;
    return prime * name.hashCode() + getData().hashCode();
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

    final Variable other = (Variable) obj;
    if (!name.equals(other.name)) {
      return false;
    }

    return getData().equals(other.getData());
  }

  @Override
  public String toString() {
    return String.format("Variable[name=%s, data=%s]", getName(), getData());
  }
}
