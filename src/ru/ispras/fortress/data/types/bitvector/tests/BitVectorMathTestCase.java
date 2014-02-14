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
