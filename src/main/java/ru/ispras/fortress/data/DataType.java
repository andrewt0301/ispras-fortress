/*
 * Copyright (c) 2012 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * DataType.java, May 12, 2012 11:06:13 AM Andrei Tatarnikov
 */

package ru.ispras.fortress.data;

import java.util.List;
import java.util.Arrays;
import java.util.HashMap;

/**
 * The DataType class stores information about data types used by the solver engine.
 * It maintains a single instance for each data type (uniqueness is based on
 * the data type identifier and the data size).   
 * 
 * @author Andrei Tatarnikov
 */

public final class DataType 
{
    /**
     * Table that stores singleton instances of data types.
     */

    private static HashMap<String, DataType> dataTypes = new HashMap<String, DataType>();

    /**
     * The LOGIC_TYPE_SIZE constant specifies the size of logic data types.
     * Such types are not related with machine-dependent types and can have 
     * any size. For this reason, we specify it as zero to distinguish from
     * types that describe real data.    
     */

    public static final int LOGIC_TYPE_SIZE = 0;

    /** Predefined logic integer type. */
    public static final DataType INTEGER = newDataType(DataTypeId.LOGIC_INTEGER);

    /** Predefined logic real type. */
    public static final DataType REAL = newDataType(DataTypeId.LOGIC_REAL);

    /** Predefined logic boolean type. */
    public static final DataType BOOLEAN = newDataType(DataTypeId.LOGIC_BOOLEAN);

    /** Predefined unknown type. */
    public static final DataType UNKNOWN = newDataType(DataTypeId.UNKNOWN);

    /**
     * Returns a type describing a bit vector of the specified size.
     *  
     * @param size Bit vector size in bits
     * @return Bit vector type
     */

    public static DataType BIT_VECTOR(int size)
    {
        if (size <= 0)
            throw new IllegalArgumentException("Illegal bit vector size: " + size);

        return newDataType(DataTypeId.BIT_VECTOR, size);
    }

    public static DataType MAP(DataType keyType, DataType valueType)
    {
        if (keyType == null || valueType == null)
            throw new NullPointerException();

        return newDataType(DataTypeId.MAP, keyType, valueType);
    }

    /**
     * Returns an instance of a data type object based on its attributes. For objects of the
     * same type (type identifier and sizes are equal), the same instance is returned.
     * 
     * @param typeId A type identifier
     * @param parameters The list of type parameters 
     * @return A data type object
     */

    public static DataType newDataType(DataTypeId typeId, int size)
    {
        if (typeId == DataTypeId.BIT_VECTOR)
            return newDataType(typeId, (Object) Integer.valueOf(size));
        return newDataType(typeId);
    }

    public static DataType newDataType(DataTypeId typeId, Object ... parameters)
    {
        if (typeId == null)
            throw new NullPointerException();

        final List<Object> list = Arrays.asList(parameters);
        typeId.validate(list);

        final String key = typeId.format(list);
        if (dataTypes.containsKey(key))
            return dataTypes.get(key);

        final DataType dataType = new DataType(typeId, key, list);
        dataTypes.put(key, dataType);

        return dataType;
    }

    /**
     * Calculates a hash value that uniquely identifies a data type. 
     * 
     * @param typeId A type identifier.
     * @param size The size of data in bits.
     * @return A hash value.
     */

    private static int calculateHashCode(DataTypeId typeId, int size)
    {
        final int prime = 31;
        int result = 1;

        result = prime * result + size;
        result = prime * result + typeId.ordinal();

        return result;
    }

    private final DataTypeId    typeId;
    private final String        name;
    private final List<Object>  parameters;

    /**
     * Constructs a data type object based on its attributes.
     * 
     * @param typeId A type identifier.
     * @param size The size of data in bits.
     */

    private DataType(DataTypeId typeId, String name, List<Object> parameters)
    {
        this.typeId = typeId;
        this.name = name;
        this.parameters = parameters;
    }

    /**
     * Returns a data type identifier.
     * 
     * @return Data type identifier.
     */

    public DataTypeId getTypeId()
    {
        return typeId;
    }

    /**
     * Returns the size of binary data in bits. Returns LOGIC_TYPE_SIZE for logic types.
     * 
     * @return Data size in bits.
     */

    public int getSize()
    {
        if (typeId == DataTypeId.BIT_VECTOR)
            return (Integer) DataTypeId.BIT_VECTOR.getAttribute(DataTypeId.Attribute.SIZE, parameters);
        return LOGIC_TYPE_SIZE;
    }

    /**
     * Returns a radix to be used for conversion data of this type to a string or vice versa.
     * 
     * @return A radix value.
     */

    public int getTypeRadix()
    {
        return typeId.radix(getSize());
    }

    /**
     * Returns the class that is used to store data (internal representation).
     * 
     * @return The class that is used to store data.
     */

    public Class<?> getValueClass()
    {
        return typeId.getValueClass();
    }

    /**
     * Creates an instance of a data object of a corresponding data type.
     * 
     * @param value The text representation of a value.
     * @param radix The radix to be used for parsing.
     * @return A new data object.
     */

    public Data valueOf(String value, int radix)
    {
        if (null == value)
            throw new NullPointerException();

    	value = value.replaceAll("\\s?", ""); // Removes extra spaces
        return new Data(this, typeId.valueOf(value, radix, parameters));
    }
    
    /**
     * Creates an uninitialized data object (the value is set to null).
     * 
     * @return A new data object.
     */

    public Data valueUninitialized()
    {
        return new Data(this, null);
    }
  
    /**
     * {@inheritDoc}
     */

    @Override
    public String toString()
    {
        return name;
    }

    /**
     * {@inheritDoc}
     */

    @Override
    public int hashCode()
    {
        return name.hashCode();
    }

    /**
     * {@inheritDoc}
     */

    @Override
    public boolean equals(Object obj)
    {
        if (this == obj) return true;
        if (obj == null) return false;

        if (getClass() != obj.getClass())
            return false;

        final DataType other = (DataType) obj;

        if (typeId != other.typeId) return false;
        if (getSize() != other.getSize()) return false;

        return getValueClass().equals(other.getValueClass());
    }
}
