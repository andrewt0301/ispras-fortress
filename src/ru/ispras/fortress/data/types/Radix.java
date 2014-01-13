/*
 * Copyright (c) 2013 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * Radix.java, Nov 5, 2013 3:56:13 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.data.types;

/**
 * The Radix enumeration describes radixes to be used to convert
 * a value to a string or vice versa.
 * 
 * @author Andrei Tatarnikov
 */

public enum Radix
{
    /** Radix for binary data.*/
    BIN(2),

    /** Radix for decimal data.*/
    DEC(10),

    /** Radix for hexadecimal data.*/
    HEX(16);

    private final int value;

    private Radix(int value)
    {
        this.value = value;
    }

    public int value()
    {
        return value;
    }
}
