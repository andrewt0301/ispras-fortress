/*
 * Copyright (c) 2012 ISPRAS
 *
 * Institute for System Programming of Russian Academy of Sciences
 *
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 *
 * All rights reserved.
 *
 * StandardOperation.java, Jan 20, 2012 12:14:03 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.expression;

/**
 * The StandardOperation.java enumeration contains identifiers that
 * specify particular operations used in expressions.
 *
 * @author Andrei Tatarnikov
 */

public enum StandardOperation
{
    /**
    The items below belong to the "Logic Operations" group.
    */

    /** Group: Logic, Operation: Equality */
    EQ,

    /** Group: Logic, Operation: Not Equal */
    NOTEQ,

    /** Group: Logic, Operation: Case equality */
    EQCASE,

    /** Group: Logic, Operation: Case not equality */
    NOTEQCASE,

    /** Group: Logic, Operation: AND */
    AND,

    /** Group: Logic, Operation: OR */
    OR,

    /** Group: Logic, Operation: NOT */
    NOT,

    /** Group: Logic, Operation: XOR */
    XOR,

    /** Group: Logic, Operation: Implication */
    IMPL,

    /** Group: Logic, Operation: Conditional expression aka if-then-else */
    ITE,

    /**
    The items below belong to the "Logic Arithmetic" group.
    */

    /** Group: Logic, Operation: Unary minus */
    MINUS,

    /** Group: Logic, Operation: Unary minus */
    PLUS,

    /** Group: Logic, Operation: Addition */
    ADD,

    /** Group: Logic, Operation: Subtraction */
    SUB,

    /** Group: Logic, Operation: Division */
    DIV,

    /** Group: Logic, Operation: Multiplication */
    MUL,

    /** Group: Logic, Operation: Remainder */
    REM,

    /** Group: Logic, Operation: Modulo */
    MOD,

    /** Group: Logic, Operation: Less */
    LESS,

    /** Group: Logic, Operation: Less or equal */
    LESSEQ,

    /** Group: Logic, Operation: Greater */
    GREATER,

    /** Group: Logic, Operation: Greater or equal */
    GREATEREQ,

    /** Group: Logic, Operation: Power */
    POWER,

    /**
    The items below belong to the "Basic Bitvector Arithmetic" group.
    */

    /** Group: Bitvector, Operation: Addition */
    BVADD,

    /** Group: Bitvector, Operation: Subtraction */
    BVSUB,

    /** Group: Bitvector, Operation: Unary minus */
    BVNEG,

    /** Group: Bitvector, Operation: Multiplication */
    BVMUL,

    /** Group: Bitvector, Operation: Unsigned remainder */
    BVUREM,

    /** Group: Bitvector, Operation: Signed remainder */
    BVSREM,

    /** Group: Bitvector, Operation: Signed modulo */
    BVSMOD,

    /** Group: Bitvector, Operation: Logical shift left */
    BVLSHL,

    /** Group: Bitvector, Operation: Arithmetical shift left */
    BVASHL,

    /** Group: Bitvector, Operation: Unsigned (BitVectorOperational) shift right */
    BVLSHR,

    /** Group: Bitvector, Operation: Signed (arithmetical) shift right */
    BVASHR,

    /** Group: Bitvector, Operation: Concatenation */
    BVCONCAT,

    /** Group: Bitvector, Operation: Replication (concatenation of several copies of bitvector) */
    BVREPEAT  (Attribute.PARAMETRIC),

    /** Group: Bitvector, Operation: Rotate left */
    BVROL     (Attribute.PARAMETRIC),

    /** Group: Bitvector, Operation: Rotate right */
    BVROR     (Attribute.PARAMETRIC),

    /** Group: Bitvector, Operation: Extension by zeros */
    BVZEROEXT (Attribute.PARAMETRIC),

    /** Group: Bitvector, Operation: Extension to the signed equivalent */
    BVSIGNEXT (Attribute.PARAMETRIC),

    /**
    The items below belong to the "Bitwise Operations" group.
    */

    /** Group: Bitvector, Operation: Bitwise OR */
    BVOR,

    /** Group: Bitvector, Operation: Bitwise XOR */
    BVXOR,

    /** Group: Bitvector, Operation: Bitwise AND */
    BVAND,

    /** Group: Bitvector, Operation: Bitwise NOT */
    BVNOT,

    /** Group: Bitvector, Operation: Bitwise NAND */
    BVNAND,

    /** Group: Bitvector, Operation: Bitwise NOR */
    BVNOR,

    /** Group: Bitvector, Operation: Bitwise XNOR */
    BVXNOR,

    /**
    The items below belong to the "Predicates over Bitvectors" group.
    */

    /** Group: Bitvector, Operation: Unsigned less or equal */
    BVULE,

    /** Group: Bitvector, Operation: Unsigned less than */
    BVULT,

    /** Group: Bitvector, Operation: Unsigned greater or equal */
    BVUGE,

    /** Group: Bitvector, Operation: Unsigned greater than */
    BVUGT,

    /** Group: Bitvector, Operation: Signed less or equal */
    BVSLE,

    /** Group: Bitvector, Operation: Signed less than */
    BVSLT,

    /** Group: Bitvector, Operation: Signed greater or equal */
    BVSGE,

    /** Group: Bitvector, Operation: Signed greater than */
    BVSGT;

    private static enum Attribute
    {
        PARAMETRIC,
        DEFAULT
    }

    private final Attribute attribute;

    private StandardOperation()
    {
        this(Attribute.DEFAULT);
    }

    private StandardOperation(Attribute attribyte)
    {
        this.attribute = attribyte;
    }

    public static boolean isParametric(Enum<?> id)
    {
        if (!id.getClass().equals((StandardOperation.class)))
            return false;

        return Attribute.PARAMETRIC == ((StandardOperation) id).attribute; 
    }
}
