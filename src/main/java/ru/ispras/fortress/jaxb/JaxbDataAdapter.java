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

/**
 * The adapter class for JAXB marshalling/unmarshalling of {@link Data} objects. Performs conversion
 * between {@link Data} and {@link JaxbData} instances.
 *
 * @author <a href="mailto:i.melnichenko@deltasolutions.ru">Igor Melnichenko</a>
 *
 * @see Data
 * @see JaxbData
 */
public class JaxbDataAdapter extends XmlAdapter<JaxbData, Data> {
  @Override
  public JaxbData marshal(final Data data) throws Exception {
    if (data == null) {
      return null;
    }

    final JaxbData jaxbData = new JaxbData();
    jaxbData.type = JaxbDataType.valueOf(data.getType().getTypeId().name());
    jaxbData.size = data.getType().getSize();
    jaxbData.value = data.getValue();

    return jaxbData;
  }

  @Override
  public Data unmarshal(final JaxbData jaxbData) throws Exception {
    if (jaxbData == null) {
      return null;
    }

    final DataType dataType = DataType.newDataType(
        DataTypeId.valueOf(jaxbData.type.name()), jaxbData.size);

    return new Data(dataType, jaxbData.value);
  }
}
