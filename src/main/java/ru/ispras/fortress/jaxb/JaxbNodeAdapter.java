/*
 * Copyright 2014-2018 ISP RAS (http://www.ispras.ru)
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

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.DataTypeId;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeValue;

import javax.xml.bind.annotation.adapters.XmlAdapter;

/**
 * The adapter class for JAXB marshalling/unmarshalling of {@link Node} objects. Performs conversion
 * between {@link Node} and {@link JaxbNode} instances.
 *
 * @author <a href="mailto:i.melnichenko@deltasolutions.ru">Igor Melnichenko</a>
 *
 * @see Node
 * @see JaxbNode
 */
public class JaxbNodeAdapter extends XmlAdapter<JaxbNode, Node> {
  @Override
  public JaxbNode marshal(final Node node) throws Exception {
    if (node == null) {
      return null;
    }

    if (node instanceof NodeValue) {
      final JaxbNodeValue jaxbNodeValue = new JaxbNodeValue();
      final Data data = ((NodeValue) node).getData();
      final DataType dataType = data.getType();
      jaxbNodeValue.type = JaxbDataType.valueOf(dataType.getTypeId().name());
      jaxbNodeValue.size = dataType.getSize();
      jaxbNodeValue.value = data.getValue().toString();

      return jaxbNodeValue;
    }

    throw new IllegalArgumentException("Unsupported Node subclass: " + node.getClass().getName());
  }

  @Override
  public Node unmarshal(final JaxbNode node) throws Exception {
    if (node == null) {
      return null;
    }

    if (node instanceof JaxbNodeValue) {
      final JaxbNodeValue jaxbNodeValue = (JaxbNodeValue) node;
      final DataTypeId typeId = DataTypeId.valueOf(jaxbNodeValue.type.name());
      final DataType type = DataType.newDataType(typeId, jaxbNodeValue.size);

      return new NodeValue(type.valueOf(jaxbNodeValue.value, type.getTypeRadix()));
    }

    throw new IllegalArgumentException("Unsupported Node subclass: " + node.getClass().getName());
  }
}
