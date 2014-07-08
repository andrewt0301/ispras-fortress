/*
 * Copyright 2014 ISP RAS (http://www.ispras.ru), UniTESK Lab (http://www.unitesk.com)
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

import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlType;
import javax.xml.bind.annotation.XmlValue;

/**
 * The class for mediation during JAXB marshalling/unmarshalling of {@link NodeValue} objects.  
 * 
 * @author <a href="mailto:i.melnichenko@deltasolutions.ru">Igor Melnichenko</a>
 */
@XmlType(name = "value")
@XmlAccessorType(value = XmlAccessType.FIELD)
public class JaxbNodeValue extends JaxbNode
{
	@XmlAttribute
	public JaxbDataType type;
	@XmlAttribute
	public int size;
	@XmlValue
    public String value;
}