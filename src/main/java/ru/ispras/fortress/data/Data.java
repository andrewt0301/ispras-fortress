/*
 * Copyright (c) 2012 ISPRAS
 *
 * Institute for System Programming of Russian Academy of Sciences
 *
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 *
 * All rights reserved.
 *
 * Data.java, May 5, 2012 3:04:57 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.data;

import java.math.BigInteger;

import ru.ispras.fortress.data.types.bitvector.BitVector;

/**
 * The Data class is a storage of data being processed. This data will be used
 * as an input or an output parameter of a constraint solver.
 *
 * @author Andrei Tatarnikov
 */

public final class Data
{
    private final DataType type;
    private final Object  value;

    /**
     * Creates a data object that has the INTEGER type from an integer value.
     *
     * @param value An integer value.
     * @return New data object.
     */

    public static Data newInteger(int value)
    {
        return new Data(DataType.INTEGER, value);
    }

    /**
     * Creates a data object that has the REAL type from an double value.
     *
     * @param value A double value.
     * @return An new data object.
     */

    public static Data newReal(double value)
    {
        return new Data(DataType.REAL, value);
    }

    /**
     * Creates a data object that has the BOOLEAN type from a boolean value.
     *
     * @param value A boolean value.
     * @return A new data object.
     */

    public static Data newBoolean(boolean value)
    {
        return new Data(DataType.BOOLEAN, value);
    }

    /**
     * Creates a data object from an object value of an unknown type (UNKNOWN will be used as target type).
     * Method for wrapping uninterpreted data that should not be passed to the solver.
     *
     * @param value A value of an unknown type.
     * @return New data object.
     */

    public static Data newUnknown(Object value)
    {
        return new Data(DataType.UNKNOWN, value);
    }

    /**
     * Creates a data object that has the BIT_VECTOR type from a BigInteger object.
     *
     * @param value A BitInteger object that stores binary data for a bit vector.
     * @param size The bit vector size (in bits).
     * @return A new data object.
     */

    public static Data newBitVector(BigInteger value, int size)
    {
        if (null == value)
            throw new NullPointerException();

        final DataType dt = DataType.BIT_VECTOR(size);
        final Object    v = BitVector.unmodifiable(BitVector.valueOf(value.toByteArray(), size));

        return new Data(dt, v);
    }

    /**
     * Creates a data object that has the BIT_VECTOR type from a string.
     * 
     * @param s Textual representation of the bit vector.
     * @param radix Radix to be used for parsing.
     * @param size Size of the resulting bit vector in bits.
     * @return A new data object.
     */

    public static Data newBitVector(String s, int radix, int size)
    {
        if (null == s)
            throw new NullPointerException();

        final DataType dt = DataType.BIT_VECTOR(size);
        final Object    v = BitVector.unmodifiable(BitVector.valueOf(s, radix, size));

        return new Data(dt, v);
    }

    /**
     * Creates a data object that has the BIT_VECTOR type from an integer value.
     * 
     * @param value Integer value to be converted.
     * @param size The bit vector size (in bits).
     * @return A new data object.
     */

    public static Data newBitVector(int value, int size)
    {
        return newBitVector((long) value, size);
    }

    /**
     * Creates a data object that has the BIT_VECTOR type from a long integer value.
     * 
     * @param value Long integer value to be converted.
     * @param size The bit vector size (in bits).
     * @return A new data object.
     */

    public static Data newBitVector(long value, int size)
    {
        final DataType dt = DataType.BIT_VECTOR(size);
        final Object    v = BitVector.unmodifiable(BitVector.valueOf(value, size));

        return new Data(dt, v);
    }

    /**
     * Constructs a data object of the specified type and
     * initializes its value with the specified value object.
     *
     * @param type  The type of the data.
     * @param value An object of related type that stores the data.
     */

    public Data(DataType type, Object value)
    {
        if (null == type)
            throw new NullPointerException();

        if (null != value && !type.getValueClass().isAssignableFrom(value.getClass()))
        {
            throw new IllegalArgumentException(
                 String.format("%s is illegal value type, %s is expected.",
                      value.getClass().getSimpleName(), type.getValueClass().getSimpleName()));
        }

        this.type  = type;
        this.value = value;
    }

    /**
     * Returns information about the type of the stored value.
     * @return An IDataType object.
     */

    public DataType getType()
    {
        return type;
    }

    /**
     * Checks whether a value assigned to the the data object.
     * 
     * @return true if a value is assigned or false otherwise.
     */

    public boolean hasValue()
    {
        return null != getValue();
    }

    /**
     * Returns an object that holds the data.   
     * @return A type-dependent object that stores the data.
     */

    public Object getValue()
    {
        return value;
    }

    @Override
    public int hashCode()
    {
        final int prime = 31;
        return prime * type.hashCode() + ((value == null) ? 0 : value.hashCode());
    }

    @Override
    public boolean equals(Object obj)
    {
        if (this == obj) return true;
        if (obj == null) return false;

        if (getClass() != obj.getClass())
            return false;

        final Data other = (Data) obj;

        if (!type.equals(other.type))
            return false;

        if (value == null)
            return (null == other.value);

        return value.equals(other.value);
    }

    @Override
    public String toString()
    {
        return String.format("Data[type=%s, value=%s]",
            type.toString(), null == value ? "uninitialized" : value.toString());
    }
}
