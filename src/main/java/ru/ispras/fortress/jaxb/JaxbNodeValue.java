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

import ru.ispras.fortress.expression.NodeValue;

import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlType;
import javax.xml.bind.annotation.XmlValue;

/**
 * The representation of {@link NodeValue} suitable for JAXB marshalling and unmarshalling. This
 * class must be used only for JAXB operations.
 *
 * @author <a href="mailto:i.melnichenko@deltasolutions.ru">Igor Melnichenko</a>
 *
 * @see NodeValue
 */
@XmlType(name = "value")
public class JaxbNodeValue extends JaxbNode {
  @XmlAttribute
  public JaxbDataType type;
  @XmlAttribute
  public int size;
  @XmlValue
  public String value;
}
