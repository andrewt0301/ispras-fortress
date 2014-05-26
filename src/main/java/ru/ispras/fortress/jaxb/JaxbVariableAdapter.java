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
 * @author <a href="mailto:i.melnichenko@deltasolutions.ru">Igor Melnichenko</a>
 */
public class JaxbVariableAdapter extends XmlAdapter<JaxbVariable, Variable>
{

	@Override
	public JaxbVariable marshal(Variable variable) throws Exception
	{
		JaxbVariable jaxbVariable = new JaxbVariable();
		jaxbVariable.name = variable.getName();
		Data data = variable.getData();
		DataType dataType = data.getType();
		jaxbVariable.type =
                JaxbDataType.valueOf(dataType.getTypeId().name());
		jaxbVariable.size = dataType.getSize();
		jaxbVariable.value = String.valueOf(data.getValue());
        return jaxbVariable;
	}

	@Override
	public Variable unmarshal(JaxbVariable jaxbVariable) throws Exception
	{
		DataTypeId typeId = DataTypeId.valueOf(jaxbVariable.type.name());
        DataType type = DataType.newDataType(typeId, jaxbVariable.size);

        if (jaxbVariable.value.equals("null"))
        {
        	return new Variable(jaxbVariable.name, type.valueUninitialized());
        }
        else
        {
        	return new Variable(jaxbVariable.name,
        	        type.valueOf(jaxbVariable.value, type.getTypeRadix()));
        }
	}
}
