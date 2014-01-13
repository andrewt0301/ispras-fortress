/*
 * Copyright (c) 2012 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * BitVectorMultiMappingTestCase.java, Nov 13, 2012 4:35:54 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.data.types.bitvector.tests;

import org.junit.Test;

import ru.ispras.fortress.data.types.bitvector.BitVector;

import static ru.ispras.fortress.data.types.bitvector.tests.TestUtils.*;

public class BitVectorMultiMappingTestCase
{
    @Test
    public void test1()
    {
        final BitVector rd1 = BitVector.valueOf("11110000");
        final BitVector rd2 = BitVector.valueOf("00110011");
        final BitVector rd3 = BitVector.valueOf("11000000");

        final BitVector  rd = BitVector.createMapping(rd1, rd2, rd3);

        checkBitVector(
            rd,
            "11000000" + "00110011" + "11110000"
            );

        rd.assign(
            BitVector.valueOf("11000011" + "11011011" + "10100001")
            );

        checkBitVector(
            rd,
            "11000011" + "11011011" + "10100001"
            );

        checkBitVector(
            rd1,
            "10100001"
            );

        checkBitVector(
            rd2,
            "11011011"
            );

        checkBitVector(
            rd3,
            "11000011"
            );
    }

    @Test
    public void test2()
    {
        final BitVector rd1 = BitVector.valueOf("0110");
        final BitVector rd2 = BitVector.valueOf("1001");

        final BitVector  rd = BitVector.createMapping(rd1, rd2);

        checkBitVector(
            rd,
            "1001" + "0110"
            );

        rd.assign(
            BitVector.valueOf("1111" + "0000")
            );

        checkBitVector(
            rd,
            "1111" + "0000"
            );

        checkBitVector(
            rd1,
            "0000"
            );

        checkBitVector(
            rd2,
            "1111"
            );
    }
    
    @Test
    public void test21()
    {
        final BitVector rd1 = BitVector.valueOf("011");
        final BitVector rd2 = BitVector.valueOf("1001");

        final BitVector rd = BitVector.createMapping(rd1, rd2);

        checkBitVector(
            rd,
            "1001" + "011"
            );

        final BitVector rdX = BitVector.valueOf("1111" + "000");
        checkBitVector(rdX, "1111" + "000");

        rd.assign(
            rdX
            );

        checkBitVector(
            rd,
            "1111" + "000"
            );

        checkBitVector(
            rd1,
            "000"
            );

        checkBitVector(
            rd2,
            "1111"
            );
    }

    @Test
    public void test3()
    {
        final BitVector rd1 = BitVector.valueOf("0010000110");
        final BitVector rd2 = BitVector.valueOf("00001001");
        final BitVector  rd = BitVector.createMapping(rd1, rd2);

        System.out.println(rd.toBinString());

        checkBitVector(
            rd,
            "00001001" + "0010000110"
            );

        /*
        rd.assign(
            RawData.valueOf("01010101" + "1100110011")
            );
        
        checkRawData(
            rd,
            "01010101" + "1100110011"
            );
        */

        final BitVector rdX = BitVector.valueOf("11110011" + "1111110011");

        rd.assign(rdX);

        checkBitVector(
            rd,
            "11110011" + "1111110011"
            );
    }

    @Test
    public void test4()
    {
        final BitVector rd1 = BitVector.valueOf("1100000000");
        final BitVector rd2 = BitVector.valueOf("00");
        final BitVector rd3 = BitVector.valueOf("111");
        final BitVector rd4 = BitVector.valueOf("1100011100");
        final BitVector  rd = BitVector.createMapping(rd1, rd2, rd3, rd4);

        System.out.println(rd.toBinString());

        checkBitVector(
            rd,
            "1100011100" + "111" + "00" + "1100000000"
            );
    }

    @Test
    public void test5()
    {
        final BitVector rd1 = BitVector.valueOf("1");
        final BitVector rd2 = BitVector.valueOf("0");
        final BitVector rd3 = BitVector.valueOf("0");
        final BitVector rd4 = BitVector.valueOf("1");
        final BitVector rd5 = BitVector.valueOf("1");
        final BitVector  rd = BitVector.createMapping(rd1, rd2, rd3, rd4, rd5);

        System.out.println(rd.toBinString());

        checkBitVector(
            rd,
            "11001"
            );

       rd.assign(
            BitVector.valueOf("00110")
            );

       checkBitVector(
            rd,
            "00110"
            );

        checkBitVector(rd1, "0");
        checkBitVector(rd2, "1");
        checkBitVector(rd3, "1");
        checkBitVector(rd4, "0");
        checkBitVector(rd5, "0");
    }

    @Test
    public void test6()
    {
        final BitVector rd1 = BitVector.valueOf("111100001");
        final BitVector rd2 = BitVector.valueOf("0000111100");
        final BitVector rd3 = BitVector.valueOf("00110110101");
        final BitVector rd4 = BitVector.valueOf("11110000");
        final BitVector rd5 = BitVector.valueOf("111");
        final BitVector  rd = BitVector.createMapping(rd1, rd2, rd3, rd4, rd5);

        System.out.println(rd.toBinString());

        checkBitVector(
            rd,
            "111" + "11110000" + "00110110101" + "0000111100" + "111100001"
            );
    }

}
