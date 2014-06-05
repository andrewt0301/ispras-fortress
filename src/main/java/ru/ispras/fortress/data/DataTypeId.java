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

import java.util.Map;
import java.util.HashMap;
import java.util.List;
import java.util.ArrayList;

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
        Object valueOf(String s, int radix, List<Object> params)
        {
            final int size = (Integer) params.get(0);
            return BitVector.unmodifiable(BitVector.valueOf(s, radix, size));
        }

        int radix(int size)
        {
            // TODO: see this code. It is simplified to always use BIN_RADIX. Probably, it could be done better.
            return Radix.BIN.value();

            // If the size if proportional to 4, we print it as a hexadecimal value. Otherwise, as a binary value.
            // return  (0 == (size % BITS_IN_HEX)) ? HEX_RADIX : BIN_RADIX;
        }

        void validate(List<Object> params)
        {
            report(params, Integer.class);
        }

        String format(List<Object> params)
        {
            return String.format("(%s %d)", name(), params.get(0));
        }

        Object getAttribute(String name, List<Object> params)
        {
            if (name.equals("size"))
                return params.get(0);

            return null;
        }
    },

    /**
     * A boolean type. It is a logic type. This means it has no connection with
     * machine-dependent types used to store boolean values (like BYTE, WORD, etc.).
     * The size attribute is not applicable.
     */
    LOGIC_BOOLEAN (Boolean.class)
    {
        Object valueOf(String s, int radix, List<Object> params)
        {
            return Boolean.valueOf(s);
        }

        int radix(int size)
        {
            return Radix.BIN.value();
        }

        void validate(List<Object> params) { report(params); }
        String format(List<Object> params) { return name(); }
    },

    /**
     * An integer type. It is a logic type. This means that it has no connection
     * with machine-dependent types used to store integer values (like 16-bit, 32-bit
     * or 64-bit integer representations). The size attribute is not applicable.
     */
    LOGIC_INTEGER (Integer.class)
    {
        Object valueOf(String s, int radix, List<Object> params)
        {
            return Integer.valueOf(s, radix);
        }

        int radix(int size)
        {
            return Radix.DEC.value();
        }

        void validate(List<Object> params) { report(params); }
        String format(List<Object> params) { return name(); }
    },

    /**
     * A real type. It is a logic type. This means that it has no connection with
     * machine-dependent types used store to floating point numbers. The size attribute is not applicable.
     */
    LOGIC_REAL (Double.class)
    {
        Object valueOf(String s, int radix, List<Object> params)
        {
            return Double.valueOf(s);
        }

        int radix(int size)
        {
            return Radix.DEC.value();
        }

        void validate(List<Object> params) { report(params); }
        String format(List<Object> params) { return name(); }
    },

    KV_STORE(Map.class)
    {
        Object valueOf(String s, int radix, List<Object> params)
        {
            final DataType keyType = (DataType) params.get(0);
            final DataType valueType = (DataType) params.get(1);

            final char LPAREN = '(';
            final char RPAREN = ')';
            final char DELIM = ':';

            final Map<Data, Data> map = new HashMap<Data, Data>() {
                @Override
                public String toString()
                {
                    final StringBuilder builder = new StringBuilder();
                    builder.append(LPAREN);
                    for (Map.Entry<Data, Data> entry : entrySet())
                        builder .append(LPAREN)
                                .append(entry.getKey().getValue().toString())
                                .append(DELIM)
                                .append(entry.getValue().getValue().toString())
                                .append(RPAREN);
                    builder.append(RPAREN);
    
                    return builder.toString();
                }
            };

            int depth = -1;
            int start = -1, end = -1;

            for (int i = 0; i < s.length(); ++i)
            {
                final char c = s.charAt(i);
                if (c == LPAREN && ++depth == 1)
                    start = i + 1;
                else if (c == RPAREN && --depth == 0)
                    map.put(keyType.valueOf(s.substring(start, end), radix),
                            valueType.valueOf(s.substring(end + 1, i), radix));
                else if (c == DELIM && depth == 1)
                    end = i;
            }
            if (depth != -1)
                throw new IllegalArgumentException("Broken string value");

            return map;
        }

        int radix(int size)
        {
            return 0;
        }

        void validate(List<Object> params) { report(params, DataType.class, DataType.class); }

        String format(List<Object> params)
        {
            return String.format("(%s %s %s)", name(), params.get(0), params.get(1));
        }

        Object getAttribute(String name, List<Object> params)
        {
            if (name.equals("key"))
                return params.get(0);
            else if (name.equals("value"))
                return params.get(1);

            return null;
        }
    },

    /**
     * Uninterpreted data, that should not be passed to solver.
     */
    UNKNOWN (Object.class)
    {
        Object valueOf(String s, int radix, List<Object> params)
        {
            throw new RuntimeException("Unable to create a value of an unknown type.");
        }

        int radix(int size)
        {
            return 0;
        }

        void validate(List<Object> params) {}

        String format(List<Object> params) { return name(); }
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

    Object valueOf(String s, int radix, int size)
    {
        final List<Object> list = new ArrayList<Object>();
        list.add(size);
        return valueOf(s, radix, list);
    }

    abstract Object valueOf(String s, int radix, List<Object> params);
    
    /**
     * Returns radix to be used to convert data of this type to a string or vice versa.
     * 
     * @param size Data size in bits (needed where applicable). 
     * @return Radix value.
     */

    abstract int radix(int size);

    abstract String format(List<Object> params);
    abstract void validate(List<Object> params);

    private static void report(List<Object> passed, Class<?> ... required)
    {
        if (passed.size() != required.length)
            throw new IllegalArgumentException("Invalid number of type parameters");

        for (int i = 0; i < passed.size(); ++i)
            if (passed.get(i).getClass() != required[i])
                throw new IllegalArgumentException("Invalid parameter type");
    }

    Object getAttribute(String name, List<Object> params) { return null; }
}
