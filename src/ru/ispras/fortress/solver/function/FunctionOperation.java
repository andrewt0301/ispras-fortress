/*
 * Copyright (c) 2013 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * FunctionOperation.java, Dec 16, 2013 4:41:13 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver.function;

public enum FunctionOperation
{
    /**
    The items below belong to the "Logic Arithmetic" group.
    */

    /** Group: Logic, Operation: Absolute value */
    ABS,

    /** Group: Logic, Operation: Minimum */
    MIN,

    /** Group: Logic, Operation: Maximum */
    MAX,

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
    BVXNORR
}
