/*
 * Copyright (c) 2012 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * BIWrapper.java, May 5, 2012 6:08:16 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.data.types;

import java.math.BigInteger;

/**
 * The BIWrapper class provides a wrapper around the BigInteger class
 * to conveniently store and convert binary data. 
 * 
 * @author Andrei Tatarnikov
 */

@Deprecated
public final class BIWrapper
{
    /**
     * The BITS_IN_HEX constant specifies the number of bit a buffer should contain 
     * to be represented by one hexadecimal character (a hexadecimal number of length 1).  
     */

    private static final int BITS_IN_HEX = 4;

    private final BigInteger value;
    private final int        size;
    private final int        radix;

    /**
     * Constructs a BIWrapper object from a BigInteger value.  
     * 
     * @param value A BitVectorWrapper object that stores data.
     * @param size  The size of the data in bits.
     * @param radix The radix that will be used in data conversions.
     */

    public BIWrapper(BigInteger value, int size, int radix)
    {
        assert null != value; 

        this.value = value;
        this.size  = size;
        this.radix = radix;
    }

    /**
     * A factory method that creates a BIWrapper object from
     * a string representation. 
     *  
     * @param value The string representation of the data.
     * @param radix The radix that will be used in to convert the string to a BigInteger object.
     * @param size  The size of the data in bits.
     * @param typeRadix The radix that will be used to convert the data object to string.
     * @return object of BitVectorWrapper
     */

    public static BIWrapper valueOf(String value, int radix, int size, int typeRadix)
    {
        return new BIWrapper(new BigInteger(value, radix), size, typeRadix);
    }

    /**
     * Converts the stored data into a binary string. 
     * @return A string representing the stored value in binary format.
     */

    public String toBinString()
    {
        final String binstr = value.toString(Radix.BIN.value());
        final int     count = size - binstr.length();

        return (count > 0) ? String.format("%0" + count + "d", 0) + binstr: binstr;
    }

    /**
     * Converts the stored data into a hexadecimal string. 
     * @return A string representing the stored value in hexadecimal format.
     */

    public String toHexString()
    {
        final String hexstr = value.toString(Radix.HEX.value());
        final int     count = size / BITS_IN_HEX - hexstr.length();

        return (count > 0) ? String.format("%0" + count + "d", 0) + hexstr: hexstr;
    }

    /**
     * Converts the stored data to a string (the string format depends on radix).
     * @return The string representation of the stored data. 
     */

    @Override
    public String toString()
    {
        if (radix == Radix.HEX.value())
            return toHexString();

        if (radix == Radix.BIN.value())
            return toBinString();

        assert false;
        return value.toString();
    }

    /**
     * Returns a BigInteger object which is the internal representation of the stored data.  
     * @return A BigInteger object that holds the data (the internal representation).
     */

    public BigInteger getValue()
    {
        return value;
    }

    /**
     * Returns the size of the stored data in bits.
     * @return Data size in bits.
     */

    public int getSize()
    {
        return size;
    }

    /**
     * Returns the radix that is used to translate data to/from a string. 
     * @return The radix value.
     */

    public int getRadix()
    {
        return radix;
    }

    /**
     * {@inheritDoc}
     */

    @Override
    public int hashCode()
    {
        final int prime = 31;
        int result = 1;

        result = prime * result + size;
        result = prime * result + value.hashCode();

        return result;
    }

    /**
     * {@inheritDoc}
     */

    @Override
    public boolean equals(Object obj)
    {
        if (this == obj) return true;
        if (obj == null) return false;
        if (getClass() != obj.getClass()) return false;

        final BIWrapper other = (BIWrapper) obj;

        if (size != other.size)
            return false;

        return value.equals(other.value);
    }
}
