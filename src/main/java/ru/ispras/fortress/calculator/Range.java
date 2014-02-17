/*
 * Copyright (c) 2013 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * Range.java, Nov 6, 2013 4:16:46 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.calculator;

/**
 * The Range class is used to specify a possible arity of an operator (unary, binary, etc.).
 * It is possible for an operator to be unary and binary at the same time or to have an unlimited
 * number of operands. The Range class allows specifying a range for the allowed number of operands.
 * 
 * @author Andrei Tatarnikov
 */

public final class Range
{
    /**
     * The Bound enumeration contains constants for specifying most common bounds for
     * the range of allowed operand numbers.
     * 
     * @author Andrei Tatarnikov
     */

    public static enum Bound
    {
        /** Bound for unary operators. */ 
        UNARY(1),

        /** Bound for binary operators. */
        BINARY(2),

        /** Bound for unlimited number of operands. */
        UNBOUNDED(-1);

        private final int value;

        private Bound(int value)
        {
            this.value = value;
        }

        /**
         * Returns the number that corresponds to the given bound constant.
         * 
         * @return Numeric value for the bound. 
         */

        public int value()
        {
            return value;
        }
    }

    /** Unary operator range. */
    public static final Range UNARY = new Range(Bound.UNARY, Bound.UNARY);

    /** Binary operator range. */
    public static final Range BINARY = new Range(Bound.BINARY, Bound.BINARY);

    /** Range for operators that can be unary and binary at the same time. */
    public static final Range UNARY_BINARY = new Range(Bound.UNARY, Bound.BINARY);

    /** Range for operators that can have one (unary) or an unbounded number of operands. */
    public static final Range UNARY_UNBOUNDED = new Range(Bound.UNARY, Bound.UNBOUNDED);

    /** Range for operators that can have two (binary) or an unbounded number of operands. */
    public static final Range BINARY_UNBOUNDED = new Range(Bound.BINARY, Bound.UNBOUNDED);

    private final int min;
    private final int max;

    /**
     * Creates a range basing on the specified bounds.
     * 
     * @param min Lower bound.
     * @param max Upper bound.
     */

    public Range(Bound min, Bound max)
    {
        this(min.value(), max.value());
    }

    /**
     * Creates a range basing on the specified boundary values.
     * 
     * @param min Lower boundary value.
     * @param max Upper boundary value.
     */

    public Range(int min, int max)
    {
        assert min > 0;
        assert (min <= max) || (max == Bound.UNBOUNDED.value());

        this.min = min;
        this.max = max;
    }

    /** 
     * Checks whether the specified value falls within the range of allowed values.
     * 
     * @param value Number of operands.
     * @return <code>true</code> if value is in the range or <code>false</code> otherwise.
     */

    public boolean isWithinRange(int value)
    {
        return (min <= value) && ((value <= max) || (Bound.UNBOUNDED.value() == max));
    }
}
