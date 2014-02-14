/*
 * Copyright (c) 2014 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * BitVectorMathTestCase.java, Feb 14, 2014 5:23:00 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.data.types.bitvector.tests;

import org.junit.Test;

import ru.ispras.fortress.data.types.bitvector.BitVector;
import ru.ispras.fortress.data.types.bitvector.BitVectorMath;

import static ru.ispras.fortress.data.types.bitvector.tests.TestUtils.*;

public class BitVectorMathTestCase
{
    @Test
    public void andTests()
    {
        checkBitVector(
            BitVectorMath.and(BitVector.valueOf(0, 32), BitVector.valueOf(0xFFFFFFFF, 32)),
            0
        );

        checkBitVector(
            BitVectorMath.and(BitVector.valueOf(0xFFFFFFFF, 32), BitVector.valueOf(0xFFFFFFFF, 32)),
            0xFFFFFFFF
        );

        checkBitVector(
            BitVectorMath.and(BitVector.valueOf(0xF0F0F0F0, 32), BitVector.valueOf(0x00FFFF00, 32)),
            0x00F0F000
        );

        checkBitVector(
            BitVectorMath.and(BitVector.valueOf("11010101001"), BitVector.valueOf("11000110011")),
            "11000100001"
        );
    }
    
    @Test
    public void orTests()
    {
        checkBitVector(
            BitVectorMath.or(BitVector.valueOf(0, 32), BitVector.valueOf(0xFFFFFFFF, 32)),
            0xFFFFFFFF
        );

        checkBitVector(
            BitVectorMath.or(BitVector.valueOf(0xF0F0F0F0, 32), BitVector.valueOf(0x0F0F0F0F, 32)),
            0xFFFFFFFF
        );

        checkBitVector(
            BitVectorMath.or(BitVector.valueOf("00010001000"), BitVector.valueOf("10000000001")),
            "10010001001"
        );

        checkBitVector(
            BitVectorMath.or(BitVector.valueOf(0xFF0FFFFFFFFFFFFFl, 64), BitVector.valueOf(0xF00F0FF0FFFF0FF0l, 64)),
            0xFF0FFFFFFFFFFFFFl
         );
    }

    @Test
    public void xorTests()
    {
        checkBitVector(
            BitVectorMath.xor(BitVector.newEmpty(32), BitVector.newEmpty(32)),
            0
        );

        checkBitVector(
            BitVectorMath.xor(BitVector.valueOf(0xFFFFFFFF, 32), BitVector.valueOf(0xFFFFFFFF, 32)),
            0
        );

        checkBitVector(
            BitVectorMath.xor(BitVector.valueOf(0xFFFFA000, 32), BitVector.valueOf(0x000AFFFF, 32)),
            0xFFF55FFF
        );

        checkBitVector(
            BitVectorMath.xor(BitVector.valueOf("11101010101"), BitVector.valueOf("01010101011")),
            "10111111110"
        );
    }

    @Test
    public void notTests()
    {
        checkBitVector(BitVector.newEmpty(11), "00000000000");
        checkBitVector(BitVectorMath.not(BitVector.newEmpty(11)), "11111111111");
        checkBitVector(BitVectorMath.not(BitVector.valueOf("01010101010")), "10101010101");
        checkBitVector(BitVectorMath.not(BitVector.valueOf("0011")), "1100");
        checkBitVector(BitVectorMath.not(BitVector.valueOf("1")), "0");
        checkBitVector(BitVectorMath.not(BitVector.valueOf(0xFFFFFFFF, 32)), 0);
        checkBitVector(BitVectorMath.not(BitVector.valueOf(0xFFFFFFFFFFFFFFFFL, 64)), 0);
    }
}
