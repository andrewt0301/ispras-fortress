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

package ru.ispras.fortress.data;

import javax.xml.bind.annotation.adapters.XmlJavaTypeAdapter;

import ru.ispras.fortress.jaxb.JaxbVariableAdapter;

/**
 * The Variable class describes a variable that can be used as input or output data in constraints.
 * 
 * @author Andrei Tatarnikov
 */

@XmlJavaTypeAdapter(JaxbVariableAdapter.class)
public final class Variable {
  private static final String ERR_ILLEGAL_ASSIGNMENT =
    "It is illegal to assign a value of type %s " + "to the %s variable of type %s.";

  private final String name;
  private Data data;

  /**
   * Constructs a variable from its name and associated data.
   * 
   * @param name Variable name.
   * @param data Data the variable refers to.
   * 
   * @throws NullPointerException if any of the parameters equals null.
   */

  public Variable(String name, Data data) {
    if (null == name) {
      throw new NullPointerException();
    }

    if (null == data) {
      throw new NullPointerException();
    }

    this.name = name;
    this.data = data;
  }

  /**
   * Constructs an uninitialized variable of the specified type. The constructed variable does not
   * refer to any data and its value is set to null.
   * 
   * @param name Variable name.
   * @param type Variable type.
   * 
   * @throws NullPointerException if any of the parameters equals null.
   */

  public Variable(String name, DataType type) {
    this(name, type != null ? type.valueUninitialized() : null);
  }

  /**
   * Constructs a full copy of the given variable object. The fields are copied by reference because
   * their types are immutable.
   * 
   * @param variable Variable object to be copied.
   */

  public Variable(Variable variable) {
    this(variable != null ? variable.name : null, variable != null ? variable.data : null);
  }

  /**
   * Assigns a new data value to the variable. The value type must match the variable type if the
   * variable type is known. If it is unknown (specified as DataType.UNKNOWN), the variable type is
   * changed to the type of the argument value.
   * 
   * @param data A data value to be assigned to the variable.
   * 
   * @throws NullPointerException if the parameter equals null.
   * @throws IllegalArgumentException if the argument value type is different from the variable type
   *         and the variable type is known.
   */

  public void setData(Data data) {
    if (null == data) {
      throw new NullPointerException();
    }

    if (!getType().equals(DataType.UNKNOWN) && !getType().equals(data.getType())) {
      throw new IllegalArgumentException(String.format(
        ERR_ILLEGAL_ASSIGNMENT, data.getType(), getName(), getType()));
    }

    this.data = data;
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
   * @return An Data object associated with the variable.
   */

  public Data getData() {
    return data;
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
   * @return <code>true</code> if the variable has a value assigned or <code>false</code> otherwise.
   */

  public boolean hasValue() {
    return data.hasValue();
  }

  @Override
  public int hashCode() {
    final int prime = 31;
    return prime * name.hashCode() + data.hashCode();
  }

  @Override
  public boolean equals(Object obj) {
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

    return data.equals(other.data);
  }

  @Override
  public String toString() {
    return String.format("Variable[name=%s, data=%s]", name, data);
  }
}
