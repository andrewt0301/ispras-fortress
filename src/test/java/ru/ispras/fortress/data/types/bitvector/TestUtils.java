/*
 * Copyright (c) 2012 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * TestUtils.java, Oct 19, 2012 11:42:28 AM Andrei Tatarnikov
 */

package ru.ispras.fortress.data.types.bitvector;

import org.junit.Assert;

public final class TestUtils
{
    private TestUtils() {}

    private static final boolean OUTPUT_DEBUG_STRINGS = true;

    private static final String SEPARATOR =
        "/" + "******************************************************************" + 
        "%n* %-64s*%n" +
        "*******************************************************************" + "/";

    public static void Trace(String text)
    {
        if (OUTPUT_DEBUG_STRINGS)
            System.out.println(text);
    }

    public static void Header(String title)
    {
        Trace(String.format(SEPARATOR, title));
    }

    public static void checkBitVector(BitVector current, String expected)
    {
        final String dataString = current.toBinString();
        Trace(String.format("Data:     %32s%nExpected: %32s", dataString, expected));

        Assert.assertTrue(
            String.format("Values do not match. %s (data) != %s (expected)", dataString, expected),
            expected.equals(dataString)
        );
    }

    public static void checkBitVector(BitVector current, int expected)
    {
        checkBitVector(current, toBinString(expected, current.getBitSize()));
    }

    public static void checkBitVector(BitVector data, long expected)
    {
        checkBitVector(data, TestUtils.toBinString(expected, data.getBitSize()));
    }

    public static String toBinString(int value, int bitSize)
    {
        final String binstr = Integer.toBinaryString(value);

        if (binstr.length() > bitSize)
            return binstr.substring(binstr.length()-bitSize, binstr.length());

        final int count = bitSize - binstr.length();
        return (count > 0) ? String.format("%0" + count + "d", 0) + binstr: binstr;
    }
    
    public static String toBinString(long value, int bitSize)
    {
        final String binstr = Long.toBinaryString(value);

        if (binstr.length() > bitSize)
            return binstr.substring(binstr.length()-bitSize, binstr.length());

        final int count = bitSize - binstr.length();
        return (count > 0) ? String.format("%0" + count + "d", 0) + binstr: binstr;
    }

    public static String comparisonMsg(int val)
    {
        switch (val)
        {
        case -1: return "<";
        case 0: return "==";
        case 1: return ">";
        default:;
        }
        return "failed to compare with";
    }

    public static void checkComparison(BitVector lhs, BitVector rhs, int expected)
    {
        final String lstr = lhs.toBinString();
        final String rstr = rhs.toBinString();
        Trace(String.format("Comparison lhs: %32s%nComparison rhs: %32s", lstr, rstr));
                                            
        int actual = lhs.compareTo(rhs);

        Assert.assertTrue(
            String.format("Wrong comparison result. %s (lhs) %s %s (rhs), expected %s",
            lstr, comparisonMsg(actual), rstr, comparisonMsg(expected)),
            actual == expected);
    }
}
