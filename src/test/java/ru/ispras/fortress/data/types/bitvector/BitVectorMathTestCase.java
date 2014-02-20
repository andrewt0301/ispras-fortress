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

package ru.ispras.fortress.data.types.bitvector;

import org.junit.Test;

import static ru.ispras.fortress.data.types.bitvector.TestUtils.*;

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
    
    @Test
    public void nandTests()
    {
        checkBitVector(
            BitVectorMath.nand(BitVector.valueOf(0, 32), BitVector.valueOf(0xFFFFFFFF, 32)),
            0xFFFFFFFF
        );

        checkBitVector(
            BitVectorMath.nand(BitVector.valueOf(0xFFFFFFFF, 32), BitVector.valueOf(0xFFFFFFFF, 32)),
            0
        );

        checkBitVector(
            BitVectorMath.nand(BitVector.valueOf(0xF0F0F0F0, 32), BitVector.valueOf(0x00FFFF00, 32)),
            0xFF0F0FFF
        );

        checkBitVector(
            BitVectorMath.nand(BitVector.valueOf("11010101001"), BitVector.valueOf("11000110011")),
            "00111011110"
        );
    }

    @Test
    public void norTests()
    {
        checkBitVector(
            BitVectorMath.nor(BitVector.valueOf(0, 32), BitVector.valueOf(0xFFFFFFFF, 32)),
            0
        );

        checkBitVector(
            BitVectorMath.nor(BitVector.valueOf(0xF0F0F0F0, 32), BitVector.valueOf(0x0F0F0F0F, 32)),
            0
        );

        checkBitVector(
            BitVectorMath.nor(BitVector.valueOf("00010001000"), BitVector.valueOf("10000000001")),
            "01101110110"
        );

        checkBitVector(
            BitVectorMath.nor(BitVector.valueOf(0xFF0FFFFFFFFFFFFFl, 64), BitVector.valueOf(0xF00F0FF0FFFF0FF0l, 64)),
            0x00F0000000000000L
        );
    }

    @Test
    public void xnorTests()
    {
        checkBitVector(
            BitVectorMath.xnor(BitVector.newEmpty(32), BitVector.newEmpty(32)),
            -1
        );

        checkBitVector(
            BitVectorMath.xnor(BitVector.valueOf(0xFFFFFFFF, 32), BitVector.valueOf(0xFFFFFFFF, 32)),
            -1
        );

        checkBitVector(
            BitVectorMath.xnor(BitVector.valueOf(0xFFFFA000, 32), BitVector.valueOf(0x000AFFFF, 32)),
            0x000AA000
        );

        checkBitVector(
            BitVectorMath.xnor(BitVector.valueOf("11101010101"), BitVector.valueOf("01010101011")),
            "01000000001"
        );
    }

    @Test
    public void shlTests()
    {
        // TODO: NEED:
        // 1. TEST FOR NEGATIVE SHIFT
        // 2. TEST FOR THE SITUATION WHEN THE SECOND ARGUMENT IS a BIT VECTOR (NOT INT)
        
        checkBitVector(
            BitVectorMath.shl(BitVector.valueOf("1111"), 2),
            "1100"
        );

        checkBitVector(
            BitVectorMath.shl(BitVector.valueOf("1111111101"), 2),
            "1111110100"
        );

        checkBitVector(
            BitVectorMath.shl(BitVector.valueOf("11111111111101"), 2),
            "11111111110100"
        );
        
        checkBitVector(
            BitVectorMath.shl(BitVector.valueOf(0xFFFFFFFF, 32), 2),
            0xFFFFFFFC
        );
        
        checkBitVector(
            BitVectorMath.shl(BitVector.valueOf(0xFFFFFFFF, 32), 16),
            0xFFFF0000
        );
        
        checkBitVector(
            BitVectorMath.shl(BitVector.valueOf(0xFFFFFFFF, 32), 19),
            0xFFF80000
        );

        checkBitVector(
            BitVectorMath.shl(BitVector.valueOf(0xFFFFFFFFFFFFFFFFL, 64), 2),
            0xFFFFFFFFFFFFFFFCL
        );

        checkBitVector(
            BitVectorMath.shl(BitVector.valueOf(0xFFFFFFFFFFFFFFFFL, 64), 32),
            0xFFFFFFFF00000000L
        );

        checkBitVector(
            BitVectorMath.shl(BitVector.valueOf(0xFFFFFFFFFFFFFFFFL, 64), 35),
            0xFFFFFFF800000000L
        );
    }

    @Test
    public void lshrTests()
    {
        // TODO: NEED:
        // 1. TEST FOR NEGATIVE SHIFT
        // 2. TEST FOR THE SITUATION WHEN THE SECOND ARGUMENT IS a BIT VECTOR (NOT INT)
        
        checkBitVector(
            BitVectorMath.lshr(BitVector.valueOf("1111"), 2),
            "0011"
        );

        checkBitVector(
            BitVectorMath.lshr(BitVector.valueOf("1101111111"), 2),
            "0011011111"
        );

        checkBitVector(
            BitVectorMath.lshr(BitVector.valueOf("10111111111111"), 2),
            "00101111111111"
        );

        checkBitVector(
            BitVectorMath.lshr(BitVector.valueOf(0xFFFFFFFF, 32), 2),
            0x3FFFFFFF
        );

        checkBitVector(
            BitVectorMath.lshr(BitVector.valueOf(0xFFFFFFFF, 32), 16),
            0x0000FFFF
        );

        checkBitVector(
            BitVectorMath.lshr(BitVector.valueOf(0xFFFFFFFF, 32), 19),
            0x00001FFF
        );

        checkBitVector(
            BitVectorMath.lshr(BitVector.valueOf(0xFFFFFFFFFFFFFFFFL, 64), 2),
            0x3FFFFFFFFFFFFFFFL
        );

        checkBitVector(
            BitVectorMath.lshr(BitVector.valueOf(0xFFFFFFFFFFFFFFFFL, 64), 32),
            0x00000000FFFFFFFFL
        );

        checkBitVector(
            BitVectorMath.lshr(BitVector.valueOf(0xFFFFFFFFFFFFFFFFL, 64), 35),
            0x000000001FFFFFFFL
        );
    }
    
    @Test
    public void ashrTests()
    {
        // TODO: NEED:
        // 1. TEST FOR NEGATIVE SHIFT
        // 2. TEST FOR THE SITUATION WHEN THE SECOND ARGUMENT IS a BIT VECTOR (NOT INT)
        
        checkBitVector(
            BitVectorMath.ashr(BitVector.valueOf("1111"), 2),
            "1111"
        );

        checkBitVector(
            BitVectorMath.ashr(BitVector.valueOf("01111"), 2),
            "00011"
        );

        checkBitVector(
            BitVectorMath.ashr(BitVector.valueOf("10111111111111"), 2),
            "11101111111111"
        );
        
        checkBitVector(
            BitVectorMath.ashr(BitVector.valueOf("00101111111111"), 2),
            "00001011111111"
        );
        
        checkBitVector(
            BitVectorMath.ashr(BitVector.valueOf(0xFFFFF0FF, 32), 2),
            0xFFFFFC3F
        );

        checkBitVector(
            BitVectorMath.ashr(BitVector.valueOf(0xF0FFFFFF, 32), 16),
            0xFFFFF0FF
        );

        checkBitVector(
            BitVectorMath.ashr(BitVector.valueOf(0xF0FFFFFF, 32), 19),
            0xFFFFFE1F
        );
        
        checkBitVector(
            BitVectorMath.ashr(BitVector.valueOf(0x7FFFF0FF, 32), 2),
            0x1FFFFC3F
        );

        checkBitVector(
            BitVectorMath.ashr(BitVector.valueOf(0x70FFFFFF, 32), 16),
            0x000070FF
        );

        checkBitVector(
            BitVectorMath.ashr(BitVector.valueOf(0x70FFFFFF, 32), 19),
            0x00000E1F
        );
        
        checkBitVector(
            BitVectorMath.ashr(BitVector.valueOf(0xFFFFFFFFFFFFF0FFL, 64), 2),
            0xFFFFFFFFFFFFFC3FL
        );

        checkBitVector(
            BitVectorMath.ashr(BitVector.valueOf(0x7FFFFFFFFFFFF0FFL, 64), 2),
            0x1FFFFFFFFFFFFC3FL
        );

        checkBitVector(
            BitVectorMath.ashr(BitVector.valueOf(0xFFF0FFFFFFFFFFFFL, 64), 32),
            0xFFFFFFFFFFF0FFFFL
        );

        checkBitVector(
            BitVectorMath.ashr(BitVector.valueOf(0x7FF0FFFFFFFFFFFFL, 64), 32),
            0x000000007FF0FFFFL
        );

        checkBitVector(
            BitVectorMath.ashr(BitVector.valueOf(0xFFF0FFFFFFFFFFFFL, 64), 35),
            0xFFFFFFFFFFFE1FFFL
        );
        
        checkBitVector(
            BitVectorMath.ashr(BitVector.valueOf(0x7FF0FFFFFFFFFFFFL, 64), 35),
            0x000000000FFE1FFFL
        );
    }

    @Test
    public void rotlTests()
    {
        checkBitVector(
            BitVectorMath.rotl(BitVector.valueOf("010011"), 2),
            "001101"
        );
        
        checkBitVector(
            BitVectorMath.rotl(BitVector.valueOf("010011"), -2),
            "110100"
        );
    }
    
    @Test
    public void rotrTests()
    {
        checkBitVector(
            BitVectorMath.rotr(BitVector.valueOf("010011"), 2),
            "110100"
        );

        checkBitVector(
            BitVectorMath.rotr(BitVector.valueOf("010011"), -2),
            "001101"
        );
    }

    @Test
    public void addTests()
    {
        checkBitVector(
            BitVectorMath.add(BitVector.valueOf(1, 32), BitVector.valueOf(256, 32)),
            257
        );

        checkBitVector(
            BitVectorMath.add(BitVector.valueOf(0, 32), BitVector.valueOf(0xFFFFFFFF, 32)),
            0xFFFFFFFF
        );

        checkBitVector(
            BitVectorMath.add(BitVector.valueOf(-1, 32), BitVector.valueOf(5, 32)),
            4
        );
    }
    
    @Test
    public void subTests()
    {
        checkBitVector(
            BitVectorMath.sub(BitVector.valueOf(0, 32), BitVector.valueOf(1, 32)),
            -1
        );

        checkBitVector(
            BitVectorMath.sub(BitVector.valueOf(-1, 32), BitVector.valueOf(-1, 32)),
            0
        );

        checkBitVector(
            BitVectorMath.sub(BitVector.valueOf(1024, 32), BitVector.valueOf(21, 32)),
            1003
        );

        checkBitVector(
            BitVectorMath.sub(BitVector.valueOf(-1, 32), BitVector.valueOf(0, 32)),
            -1
        );
    }
    
    @Test
    public void negTests()
    {
        checkBitVector(BitVectorMath.neg(BitVector.newEmpty(11)),   "00000000000");
        checkBitVector(BitVectorMath.neg(BitVector.valueOf(1, 11)), "11111111111");
        checkBitVector(BitVectorMath.neg(BitVector.valueOf(-2, 11)), 2);
        checkBitVector(BitVectorMath.neg(BitVector.valueOf("1")), "1");
        checkBitVector(BitVectorMath.neg(BitVector.valueOf(256, 32)), -256);

        checkBitVector(BitVectorMath.neg(BitVector.valueOf(0xFFFFFFFF, 32)), 1);
        checkBitVector(BitVectorMath.neg(BitVector.valueOf(1, 32)), 0xFFFFFFFF);

        checkBitVector(BitVectorMath.neg(BitVector.valueOf(0xFFFFFFFFFFFFFFFFL, 64)), 1);
        checkBitVector(BitVectorMath.neg(BitVector.valueOf(1, 64)), 0xFFFFFFFFFFFFFFFFL);
    }

    @Test
    public void uleTests()
    {
        checkBitVector(BitVectorMath.ule(BitVector.newEmpty(16), BitVector.newEmpty(16)), BitVector.TRUE);
        checkBitVector(BitVectorMath.ule(BitVector.valueOf(-1, 16), BitVector.valueOf(0, 16)), BitVector.FALSE);
        checkBitVector(BitVectorMath.ule(BitVector.valueOf(-1, 16), BitVector.valueOf(-1, 16)), BitVector.TRUE);
        checkBitVector(BitVectorMath.ule(BitVector.valueOf(0xFFFF, 16), BitVector.valueOf(0xFFFF, 16)), BitVector.TRUE);
        checkBitVector(BitVectorMath.ule(BitVector.valueOf(0xFFFF, 16), BitVector.valueOf(0xFF0F, 16)), BitVector.FALSE);
        checkBitVector(BitVectorMath.ule(BitVector.valueOf(0x7FFF, 16), BitVector.valueOf(0x7FFF, 16)), BitVector.TRUE);
        checkBitVector(BitVectorMath.ule(BitVector.valueOf(0x7FFE, 16), BitVector.valueOf(0x7FFF, 16)), BitVector.TRUE);
        checkBitVector(BitVectorMath.ule(BitVector.valueOf(0x7FFF, 16), BitVector.valueOf(0x7FFE, 16)), BitVector.FALSE);
    }

    @Test
    public void ultTests()
    {
    }

    @Test
    public void ugeTests()
    {
    }

    @Test
    public void ugtTests()
    {
    }
    
    @Test
    public void sleTests()
    {    
    }
    
    @Test
    public void sltTests()
    {
    }
    
    @Test
    public void sgeTests()
    {
    }
    
    @Test
    public void sgtTests()
    {
    }
}
