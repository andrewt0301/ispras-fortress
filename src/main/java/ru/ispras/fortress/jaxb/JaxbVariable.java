package ru.ispras.fortress.jaxb;

import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlValue;

/**
 * The class for mediation during JAXB marshalling/unmarshalling of {@link Variable} objects.  
 * 
 * @author <a href="mailto:i.melnichenko@deltasolutions.ru">Igor Melnichenko</a>
 */
public class JaxbVariable
{
	@XmlAttribute
	public String name;
	@XmlAttribute
	public JaxbDataType type;
	@XmlAttribute
	public int size;
	@XmlValue
    public String value;
}
