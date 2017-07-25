/*
 * Copyright 2014 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.jaxb;

import javax.xml.bind.annotation.adapters.XmlAdapter;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.DataTypeId;
import ru.ispras.fortress.data.Variable;

/**
 * The adapter class for JAXB marshalling/unmarshalling of {@link Variable} objects. Performs
 * conversion between {@link Variable} and {@link JaxbVariable} instances.
 *
 * @see Variable
 * @see JaxbVariable
 */
public class JaxbVariableAdapter extends XmlAdapter<JaxbVariable, Variable> {
  @Override
  public JaxbVariable marshal(final Variable variable) throws Exception {
    if (variable == null) {
      return null;
    }

    final JaxbVariable jaxbVariable = new JaxbVariable();
    jaxbVariable.name = variable.getName();
    final Data data = variable.getData();
    final DataType dataType = data.getType();
    jaxbVariable.type = JaxbDataType.valueOf(dataType.getTypeId().name());
    jaxbVariable.size = dataType.getSize();
    jaxbVariable.value = String.valueOf(data.getValue());

    return jaxbVariable;
  }

  @Override
  public Variable unmarshal(final JaxbVariable jaxbVariable) throws Exception {
    if (jaxbVariable == null) {
      return null;
    }

    final DataTypeId typeId = DataTypeId.valueOf(jaxbVariable.type.name());
    final DataType type = DataType.newDataType(typeId, jaxbVariable.size);

    if (jaxbVariable.value.equals("null")) {
      return new Variable(jaxbVariable.name, type.valueUninitialized());
    } else {
      return new Variable(jaxbVariable.name, type.valueOf(jaxbVariable.value, type.getTypeRadix()));
    }
  }
}
