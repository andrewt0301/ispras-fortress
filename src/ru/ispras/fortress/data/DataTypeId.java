/*
 * Copyright (c) 2012 ISPRAS
 *
 * Institute for System Programming of Russian Academy of Sciences
 *
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 *
 * All rights reserved.
 *
 * DataTypeId.java, Apr 27, 2012 1:48:15 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.data;

import ru.ispras.fortress.data.types.Radix;
import ru.ispras.fortress.data.types.bitvector.BitVector;

/**
 * The DataTypeId enumeration is used to specify type of data a solver operates with.
 *
 * @author Andrei Tatarnikov
 */

public enum DataTypeId
{
    /**
     * A bit vector type. Represents some data buffer of a specified size.
     */
    BIT_VECTOR (BitVector.class)
    {
        Object valueOf(String s, int radix, int size)
        { 
            return BitVector.unmodifiable(BitVector.valueOf(s, radix, size));
        }

        int radix(int size)
        {
            // TODO: see this code. It is simplified to always use BIN_RADIX. Probably, it could be done better.
            return Radix.BIN.value();

            // If the size if proportional to 4, we print it as a hexadecimal value. Otherwise, as a binary value.
            // return  (0 == (size % BITS_IN_HEX)) ? HEX_RADIX : BIN_RADIX;
        }
    },

    /**
     * A boolean type. It is a logic type. This means it has no connection with
     * machine-dependent types used to store boolean values (like BYTE, WORD, etc.).
     * The size attribute is not applicable.
     */
    LOGIC_BOOLEAN (Boolean.class)
    {
        Object valueOf(String s, int radix, int size)
        {
            return Boolean.valueOf(s);
        }

        int radix(int size)
        {
            return Radix.BIN.value();
        }
    },

    /**
     * An integer type. It is a logic type. This means that it has no connection
     * with machine-dependent types used to store integer values (like 16-bit, 32-bit
     * or 64-bit integer representations). The size attribute is not applicable.
     */
    LOGIC_INTEGER (Integer.class)
    {
        Object valueOf(String s, int radix, int size)
        {
            return Integer.valueOf(s, radix);
        }

        int radix(int size)
        {
            return Radix.DEC.value();
        }
    },

    /**
     * A real type. It is a logic type. This means that it has no connection with
     * machine-dependent types used store to floating point numbers. The size attribute is not applicable.
     */
    LOGIC_REAL (Double.class)
    {
        Object valueOf(String s, int radix, int size)
        {
            return Double.valueOf(s);
        }

        int radix(int size)
        {
            return Radix.DEC.value();
        }
    },

    /**
     * Uninterpreted data, that should not be passed to solver.
     */
    UNKNOWN (Object.class)
    {
        Object valueOf(String s, int radix, int size)
        {
            throw new RuntimeException("Unable to create a value of an unknown type.");
        }

        int radix(int size)
        {
            return 0;
        }
    };

    private final Class<?> valueClass;

    /**
     * Creates a description of a data type.
     * 
     * @param valueClass The type of the object used to store the data (internal representation).
     */

    private DataTypeId(Class<?> valueClass)
    {
        this.valueClass = valueClass;
    }

    /**
     * Returns information on the type used to store the data (internal representation).
     * 
     * @return Value type.
     */

    Class<?> getValueClass()
    {
        return valueClass;
    }

    /**
     * Creates a value of the given type (described by the valueClass type) basing
     * on its textual representation.
     * 
     * @param s Textual representation of the value.
     * @param radix Radix to be used for conversion.
     * @param size Data size in bits.
     * @return Value of the given type packed into an Object value.
     */

    abstract Object valueOf(String s, int radix, int size);

    /**
     * Returns radix to be used to convert data of this type to a string or vice versa.
     * 
     * @param size Data size in bits (needed where applicable). 
     * @return Radix value.
     */

    abstract int radix(int size);
}
