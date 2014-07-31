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

    /** Group: Logic, Operation: Unary plus */
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
    The items below belong to the "Logic Arithmetic (Additional)" group.
    */

    /** Group: Logic, Operation: Absolute value */
    ABS,

    /** Group: Logic, Operation: Minimum */
    MIN,

    /** Group: Logic, Operation: Maximum */
    MAX,

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
    BVREPEAT  (1),

    /** Group: Bitvector, Operation: Rotate left */
    BVROL     (1),

    /** Group: Bitvector, Operation: Rotate right */
    BVROR     (1),

    /** Group: Bitvector, Operation: Extension by zeros */
    BVZEROEXT (1),

    /** Group: Bitvector, Operation: Extension to the signed equivalent */
    BVSIGNEXT (1),

    /** Group: Bitvector, Operation: Extraction of subvector */
    BVEXTRACT (2),

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
    BVSGT,

    /**
     * The items below belong to the "Bit Vector Reduction Operations" group.
     * 
     * Operation semantics:
     * <pre>
     * From IEEE Standard for Verilog Hardware Description Language:
     *
     * The unary reduction operators shall perform a bitwise operation on a single operand
     * to produce a single-bit result. For reduction and, reduction or, and reduction xor operators,
     * the first step of the operation shall apply the operator between the first bit of the operand
     * and the second. The second and subsequent steps shall apply the operator between the 1-bit result
     * of the prior step and the next bit of the operand using the same logic table. For reduction nand,
     * reduction nor, and reduction xnor operators, the result shall be computed by inverting the result
     * of the reduction and, reduction or, and reduction xor operation, respectively.
     * 
     * See the manual for details.
     * </pre>
     */

    /** Group: Bit Vector Reduction, Operation: Reduction AND (&) */
    BVANDR,

    /** Group: Bit Vector Reduction, Operation: Reduction NAND (~&) */
    BVNANDR,

    /** Group: Bit Vector Reduction, Operation: Reduction OR (|) */
    BVORR,

    /** Group: Bit Vector Reduction, Operation: Reduction NOR (~|) */
    BVNORR,
    
    /** Group: Bit Vector Reduction, Operation: Reduction XOR (^) */
    BVXORR,
    
    /** Group: Bit Vector Reduction, Operation: Reduction XNOR (~^) */
    BVXNORR,

    /**
    The items below belong to the "Array Operations" group.
    */

    /** Group: Array, Operation: Get stored value */
    SELECT,

    /** Group: Array, Operation: Store value */
    STORE;

    private final int numParams;

    private StandardOperation()
    {
        this(0);
    }

    private StandardOperation(int numParams)
    {
        this.numParams = numParams;
    }

    public static boolean isParametric(Enum<?> id)
    {
        return getParameterCount(id) != 0;
    }

    public static int getParameterCount(Enum<?> id)
    {
        if (!id.getClass().equals((StandardOperation.class)))
            return 0;
        return ((StandardOperation) id).numParams;
    }
}
