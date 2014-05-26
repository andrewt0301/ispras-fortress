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

import javax.xml.bind.annotation.adapters.XmlAdapter;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.DataTypeId;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeValue;

/**
 * The adapter class for JAXB marshalling/unmarshalling of {@link Node} objects. Performs
 * conversion between {@link Node} and {@link JaxbNode} instances.
 * 
 * @author <a href="mailto:i.melnichenko@deltasolutions.ru">Igor Melnichenko</a>
 */
public class JaxbNodeAdapter extends XmlAdapter<JaxbNode, Node>
{
    @Override
    public JaxbNode marshal(Node node) throws Exception
    {
    	if (node instanceof NodeValue)
    	{
    	    JaxbNodeValue jaxbNodeValue = new JaxbNodeValue();
    	    Data data = ((NodeValue) node).getData();
    	    DataType dataType = data.getType();
            jaxbNodeValue.type = JaxbDataType.valueOf(dataType.getTypeId().name());
            jaxbNodeValue.size = dataType.getSize();
            jaxbNodeValue.value = data.getValue().toString();
            return jaxbNodeValue;
    	}
    	else
    	{
    		throw new IllegalArgumentException("Only NodeValue currently supported in JAXB among "
    		        + "successors of the Node class");
    	}
    }

    @Override
    public Node unmarshal(JaxbNode node) throws Exception
    {
    	if (node instanceof JaxbNodeValue)
    	{
    		JaxbNodeValue jaxbNodeValue = (JaxbNodeValue) node;
    	    DataTypeId typeId = DataTypeId.valueOf(jaxbNodeValue.type.name());
            DataType type = DataType.newDataType(typeId, jaxbNodeValue.size);
            return new NodeValue(type.valueOf(jaxbNodeValue.value, type.getTypeRadix()));
    	}
    	else
    	{
    	    throw new IllegalArgumentException("Only NodeValue currently supported in JAXB among "
    	        + "successors of the Node class");
    	}
    	
    }
}
