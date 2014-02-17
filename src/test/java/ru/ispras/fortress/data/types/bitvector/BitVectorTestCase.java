/*
 * Copyright (c) 2012 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * BitVectorTestCase.java, Oct 17, 2012 2:36:56 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.data.types.bitvector;

import java.math.BigInteger;

import ru.ispras.fortress.data.types.bitvector.BitVector;

import org.junit.Assert;
import org.junit.Test;

import static ru.ispras.fortress.data.types.bitvector.TestUtils.*;

public class BitVectorTestCase
{
    @Test
    public void creationTests()
    {
        Header("Tests for the createEmpty and valueOf methods.");

        /////////////////////////////////////////////////////////////////////////////////////
        // Tests for createEmpty(int bitSize)

        checkBitVector(BitVector.newEmpty(11), "00000000000");

        /////////////////////////////////////////////////////////////////////////////////////
        // Tests for valueOf(final int value, final int bitSize)

        checkBitVector(BitVector.valueOf(1, 1),   1);
        checkBitVector(BitVector.valueOf(0, 1), "0");

        checkBitVector(BitVector.valueOf(-1, 32),       -1);
        checkBitVector(BitVector.valueOf(-1, 7), "1111111");

        checkBitVector(BitVector.valueOf(0, 4),    0);
        checkBitVector(BitVector.valueOf(0, 33),   0);
        checkBitVector(BitVector.valueOf(-1, 35), -1);

        { final String binStr = "1110111";
          checkBitVector(BitVector.valueOf(Integer.valueOf(binStr, 2), binStr.length()), binStr); }

        { final String binStr = "1100101010011";
          checkBitVector(BitVector.valueOf(Integer.valueOf(binStr, 2), binStr.length()), binStr); }

        /////////////////////////////////////////////////////////////////////////////////////
        // Tests for valueOf(final long value, final int bitSize)

        checkBitVector(BitVector.valueOf(0xFFFFL, 64), 0xFFFFL);
        checkBitVector(BitVector.valueOf(0xFFFF0000L, 64), 0xFFFF0000L);

        checkBitVector(BitVector.valueOf(0xFFFF0000FFFF0000L, 65), 0xFFFF0000FFFF0000L);
        
        /////////////////////////////////////////////////////////////////////////////////////
        // Tests for valueOf(final String bs, final int bitSize) and valueOf(final String bs)

        checkBitVector(BitVector.valueOf("0101010011100110000"), "0101010011100110000");
        checkBitVector(BitVector.valueOf("1101010011100110001"), "1101010011100110001");

        checkBitVector(BitVector.valueOf("11111", 2, 8), "00011111");
        checkBitVector(BitVector.valueOf("11111", 2, 9), "000011111");

        checkBitVector(BitVector.valueOf("111011", 2, 8), "00111011");
        checkBitVector(BitVector.valueOf("11111111111011", 2, 9), "111111011");
    }
    
    ////////////////////////////////////////////////////////////////////////////////////
    // COPY CONSTRUCTOR, ASSIGN AND RESET TESTS 
    ////////////////////////////////////////////////////////////////////////////////////

    @Test
    public void copyingTests()
    {
        // Some representative test data (with odd length).
        final String SAMPLE_35BIT = "101"+"10101010"+"10101010"+"10101010"+"10101010";
        
        Header("Copying Tests");
        
        //////////////////////////////////////////////////////////
        // Test case 0: creates an empty data array and assigns data to it.
        
        final BitVector rd01 = BitVector.newEmpty(35);

        checkBitVector(
            rd01,
            0 
        );
        
        final BitVector rd02 = BitVector.valueOf(Long.valueOf(SAMPLE_35BIT, 2), 35);
        
        checkBitVector(
            rd02,
            SAMPLE_35BIT 
        );
        
        rd01.assign(rd02);
        
        checkBitVector(
            rd01,
            SAMPLE_35BIT 
        );
        
        checkBitVector(
            rd02,
            SAMPLE_35BIT 
        );
        
        // We call reset to make sure we deal with a copy of the data.
        rd02.reset();
        
        checkBitVector(
            rd02,
            0 
        );
        
        checkBitVector(
            rd01,
            SAMPLE_35BIT 
        );
        
        // In this test case, we call reset to make sure we deal with a copy of the data.
        rd01.reset();

        checkBitVector(
            rd01,
            0 
        );
        
        //////////////////////////////////////////////////////////
        // Test case 1: the assign and reset methods 
        
        final BitVector rd11 = BitVector.valueOf(Long.valueOf(SAMPLE_35BIT, 2), 35);
        final BitVector rd12 = BitVector.valueOf(Long.valueOf("11111111111111111", 2), 35);

        rd11.assign(rd12);
        
        checkBitVector(
            rd12,
            "00000000000000000011111111111111111" 
        );
        
        // We call reset to make sure we deal with a copy of the data.
        rd12.reset();
        
        checkBitVector(
            rd11,
            "00000000000000000011111111111111111" 
        );
            
        checkBitVector(
            rd12,
            0 
        );

        // In this test case, we call reset to make sure we deal with a copy of the data.
        rd11.reset();

        checkBitVector(
            rd11,
            0 
        );

        //////////////////////////////////////////////////////////
        // Test case 2: the copy constructor

        final BitVector rd21 = BitVector.valueOf(Long.valueOf(SAMPLE_35BIT, 2), 35);
        final BitVector rd22 = BitVector.copyOf(rd21);
        
        checkBitVector(
            rd21,
            SAMPLE_35BIT 
        );
        
        checkBitVector(
            rd22,
            SAMPLE_35BIT 
        );
        
        // We call reset to make sure we deal with a copy of the data.
        rd21.reset();
        
        checkBitVector(
            rd21,
            0 
        );
            
        checkBitVector(
            rd22,
            SAMPLE_35BIT 
        );
        
        // We call reset to make sure we deal with a copy of the data.
        rd22.reset();
        
        checkBitVector(
            rd21,
            0 
        );
            
        checkBitVector(
            rd22,
            0 
        );
        
        //////////////////////////////////////////////////////////
        // Test case 3: assignment with truncation
        
        // NOTE: NO IMPLICIT CONVERSIONS ARE ALLOWED.
        // TO MAKE OPERATIONS IWTH DIFFERENT TYPES, WE NEED TO COERCE THEN EXPLICITLY.
        
        /*
        final RawData rd31 = new RawDataStore(27);

        checkRawData(
            rd31,
            0 
        );
        
        final RawData rd32 = new Int(Long.valueOf(SAMPLE_35BIT, 2), 35).getRawData();
        
        checkRawData(
            rd32,
            SAMPLE_35BIT 
        );
        
        rd31.assign(rd32);
        
        checkRawData(
            rd31,
            "010"+"10101010"+"10101010"+"10101010" 
        );
        
        checkRawData(
            rd32,
            SAMPLE_35BIT 
        );
        */
    }
    
    ////////////////////////////////////////////////////////////////////////////////////
    // READING MAPPING TESTS 
    ////////////////////////////////////////////////////////////////////////////////////

    @Test
    public void mappingReadingTests()
    {
        Header("Mapping Reading Tests");

        // Some representative test data (with odd length).
        final String SAMPLE_35BIT_BIN_STR = "101"+"10101010"+"10101010"+"10101010"+"10101010";

        

        Trace(BitVector.valueOf(0xFF, 32).toBinString());
        Trace(BitVector.valueOf(0xFF00FF00, 32).toBinString());

        checkBitVector(
           BitVector.newMapping(BitVector.valueOf(-1, 32), 0, 32),
           -1
        );

        checkBitVector(
            BitVector.newMapping(BitVector.valueOf(0xFF00FF00, 32), 0, 32),
            0xFF00FF00
        );

        // NOT ALLOWED (ASSERTION)
        /*checkRawData(
            BitVector.createMapping(BitVector.valueOf(-1, 32), 0, 0),
            ""   
        );*/
        
        ////////////////////////////////////////////////////////////
        // Test for multiple of 8 data arrays (no incomplete bytes).

        checkBitVector(
            BitVector.newMapping(BitVector.valueOf(0xFF00FF00, 32), 0, 8),
            0x00
        );

        checkBitVector(
            BitVector.newMapping(BitVector.valueOf(0xFF00FF00, 32), 8, 8),
            0xFF
        );
        
        checkBitVector(
            BitVector.newMapping(BitVector.valueOf(0xFF00FF00, 32), 16, 8),
            0x00
        );
        
        checkBitVector(
            BitVector.newMapping(BitVector.valueOf(0xFF00FF00, 32), 24, 8),
            0xFF
        );
        
        
        checkBitVector(
            BitVector.newMapping(BitVector.valueOf(0xFF00FF00, 32), 4, 8),
            0xF0
        );
        
        checkBitVector(
            BitVector.newMapping(BitVector.valueOf(0xFF00FF00, 32), 20, 8),
            0xF0
        );
       
        checkBitVector(
            BitVector.newMapping(BitVector.valueOf(0xFF00FF00, 32), 4, 16),
            0x0FF0
        );
        
        checkBitVector(
            BitVector.newMapping(BitVector.valueOf(0xFF00FF00, 32), 12, 16),
            0xF00F
        );
        
        ////////////////////////////////////////////////////////////
        // Test for data arrays with an incomplete high byte (size is not multiple of 8)

        checkBitVector(
            BitVector.newMapping(BitVector.valueOf(-1L, 35), 0, 35),
            -1L
        );

        checkBitVector(
            BitVector.newMapping(BitVector.valueOf(Long.valueOf("11" + SAMPLE_35BIT_BIN_STR, 2), 35), 0, 35),
            SAMPLE_35BIT_BIN_STR 
        );

        checkBitVector(
            BitVector.newMapping(BitVector.valueOf(Long.valueOf(SAMPLE_35BIT_BIN_STR, 2), 35), 27, 8),
            "101"+"10101" 
        );

        checkBitVector(
            BitVector.newMapping(BitVector.valueOf(Long.valueOf(SAMPLE_35BIT_BIN_STR, 2), 35), 24, 11),
            "101"+"10101010" 
        );

        checkBitVector(
            BitVector.newMapping(BitVector.valueOf(Long.valueOf(SAMPLE_35BIT_BIN_STR, 2), 35), 23, 11),
            "01"+"101010101" 
        );

        checkBitVector(
            BitVector.newMapping(BitVector.valueOf(Long.valueOf("11" + SAMPLE_35BIT_BIN_STR, 2), 35), 1, 5),
            "10101" 
        );

        checkBitVector(
            BitVector.newMapping(BitVector.valueOf(Long.valueOf("11" + SAMPLE_35BIT_BIN_STR, 2), 35), 2, 15),
            "0"+"10101010"+"101010" 
        );
        
        checkBitVector(
            BitVector.newMapping(BitVector.valueOf(Long.valueOf("11" + SAMPLE_35BIT_BIN_STR, 2), 35), 8, 4),
            "1010" 
        );
        
        checkBitVector(
            BitVector.newMapping(BitVector.valueOf(0xFF00FF00, 29), 5, 23),
            "11110000000011111111000"
        );
        
        checkBitVector(
            BitVector.newMapping(BitVector.valueOf(Long.valueOf("11" + SAMPLE_35BIT_BIN_STR, 2), 35), 25, 10),
            "101"+"1010101" 
        );
        
        checkBitVector(
            BitVector.newMapping(BitVector.valueOf(0x00FFFFFF, 32), 22, 10),
            "0000000011" 
        );        
    }
    
    ////////////////////////////////////////////////////////////////////////////////////
    // WRITING MAPPING TESTS
    ////////////////////////////////////////////////////////////////////////////////////
    
    @Test
    public void mappingWritingTests()
    {
        Header("Mapping Writing Tests");
        
        // Some representative test data (with odd length).
        final String SAMPLE_35BIT_BIN_STR = "101"+"10101010"+"10101010"+"10101010"+"10101010";
        
        
        
        //////////////////////////////////////////////////////////
        // Test Case 1: Mapping size equals source size.
        
        final BitVector rd01 = BitVector.valueOf(Long.valueOf(SAMPLE_35BIT_BIN_STR, 2), 35);
        
        checkBitVector(
            rd01,
            SAMPLE_35BIT_BIN_STR 
        );
        
        final BitVector rd02 = BitVector.valueOf(0xF0F00F, 35);
        
        checkBitVector(
            rd02,
            0xF0F00F 
        );
        
        final BitVector rdm01 = BitVector.newMapping(rd01, 0, rd01.getBitSize());
        
        checkBitVector(
            rdm01,
            SAMPLE_35BIT_BIN_STR 
        );
        
        rdm01.assign(rd02);
        
        checkBitVector(
            rd01,
            0xF0F00F 
        );
          
        checkBitVector(
            rd02,
            0xF0F00F 
        );
        
        checkBitVector(
            rdm01,
            0xF0F00F 
        );
        
        rd02.reset();

        checkBitVector(
            rd01,
            0xF0F00F 
        );

        checkBitVector(
            rd02,
            0
        );

        checkBitVector(
            rdm01,
            0xF0F00F 
        );
        
        rdm01.reset();
        
        checkBitVector(
            rd01,
            0 
        );

        checkBitVector(
            rd02,
            0
        );

        checkBitVector(
            rdm01,
            0 
        );

        //////////////////////////////////////////////////////////
        // Test Case 2: Mapped region is located in the middle of the source data
        // array (the offset and the mapping length is multiple of 8).
        
        final BitVector rd11 = BitVector.valueOf(Long.valueOf(SAMPLE_35BIT_BIN_STR, 2), 35);
        
        checkBitVector(
            rd11,
            SAMPLE_35BIT_BIN_STR 
        );
        
        final BitVector rd12 = BitVector.valueOf(0xFF, 8);
        
        checkBitVector(
            rd12,
            0xFF 
        );
        
        final BitVector rdm11 = BitVector.newMapping(rd11, 8, 8);
        
        checkBitVector(
            rdm11,
            "10101010" 
        );
        
        rdm11.assign(rd12);
        
        checkBitVector(
            rdm11,
            0xFF 
        );
        
        checkBitVector(
           rd11,
           "10110101010101010101111111110101010" 
        );

        //////////////////////////////////////////////////////////
        // Test Case 3: Mapped region is located in the middle of the source data
        // array (the offset and the mapping length is multiple of 8).
        
        final BitVector rd31 = BitVector.valueOf(Long.valueOf(SAMPLE_35BIT_BIN_STR, 2), 35);
        
        checkBitVector(
            rd31,
            SAMPLE_35BIT_BIN_STR 
        );
        
        final BitVector rd32 = BitVector.valueOf(0xFFFF, 11);
        
        checkBitVector(
            rd32,
            0xFFFF 
        );
        
        final BitVector rdm31 = BitVector.newMapping(rd31, 3, 11);
        
        checkBitVector(
            rdm31,
            "10101010101" 
        );
        
        rdm31.assign(rd32);

        checkBitVector(
            rd31,
            "10110101010101010101011111111111010" 
        );
                
        checkBitVector(
            rd32,
            "11111111111" 
        );

        checkBitVector(
            rdm31,
            0xFFFF 
        );
        
        rdm31.reset();
        
        checkBitVector(
            rd31,
            "10110101010101010101000000000000010"
        );
                   
        checkBitVector(
            rd32,
            "11111111111" 
        );

        checkBitVector(
            rdm31,
            0 
        );

        
        //////////////////////////////////////////////////////////
        // Test Case 4: Mapped region is located in the middle of the source data
        // array (the offset is multiple of 8 and the mapping length is not multiple of 8).

        final BitVector rd41 = BitVector.valueOf(Long.valueOf(SAMPLE_35BIT_BIN_STR, 2), 35);

        checkBitVector(
            rd41,
            SAMPLE_35BIT_BIN_STR 
        );

        final BitVector rd42 = BitVector.valueOf(0xFF, 5);

        checkBitVector(
            rd42,
            0xFF 
        );

        final BitVector rdm41 = BitVector.newMapping(rd41, 8, 5);

        checkBitVector(
            rdm41,
            "01010" 
        );

        rdm41.assign(rd42);

        checkBitVector(
            rd41,
            "10110101010101010101011111110101010" 
        );

        checkBitVector(
            rd42,
            "11111" 
        );
        
        checkBitVector(
            rdm41,
            "11111" 
        );
        
        /*
        rdm31.reset();
        
        checkRawData(
            rd31,
            "10110101010101010101000000000000010"
        );
                   
        checkRawData(
            rd32,
            "11111111111" 
        );

        checkRawData(
            rdm31,
            0 
        );*/
        
        //////////////////////////////////////////////////////////
        // Test Case 5: Mapped region is located in the middle of the source data
        // array (the offset is multiple of 8 and the mapping length is not multiple of 8).

        final BitVector rd51 = BitVector.valueOf(Long.valueOf(SAMPLE_35BIT_BIN_STR, 2), 35);

        checkBitVector(
            rd51,
            SAMPLE_35BIT_BIN_STR 
        );

        final BitVector rd52 = BitVector.valueOf(0, 5);

        checkBitVector(
            rd52,
            0 
        );

        final BitVector rdm51 = BitVector.newMapping(rd51, 8, 5);

        checkBitVector(
            rdm51,
            "01010"
        );

        rdm51.assign(rd52);

        checkBitVector(
            rd51,
            "10110101010101010101010000010101010" 
        );

        checkBitVector(
            rd52,
            0 
        );
        
        checkBitVector(
            rdm51,
            0 
        );
        
        //////////////////////////////////////////////////////////
        // Test Case 6: Mapped region is located in the middle of the source data
        // array (the offset is multiple of 8 and the mapping length is not multiple of 8).

        final BitVector rd61 = BitVector.valueOf(0, 35);
        Assert.assertTrue(
                BitVector.valueOf("0101010011100110000").toBinString().equals("0101010011100110000"));

            Assert.assertTrue(
                BitVector.valueOf("0101010011100110000").toBinString().equals("0101010011100110000"));

            Assert.assertTrue(
                BitVector.valueOf("11111", 2, 8).toBinString().equals("00011111"));

            Assert.assertTrue(
                BitVector.valueOf("111011", 2, 8).toBinString().equals("00111011"));

            Assert.assertTrue(
                BitVector.valueOf("11111111111011", 2, 8).toBinString().equals("11111011"));
        checkBitVector(
            rd61,
            0 
        );

        final BitVector rd62 = BitVector.valueOf(0xFF, 5);

        checkBitVector(
            rd62,
            0xFF 
        );

        final BitVector rdm61 = BitVector.newMapping(rd61, 1, 5);

        checkBitVector(
            rdm61,
            "00000"
        );

        rdm61.assign(rd62);

        checkBitVector(
            rd61,
            "00000000000000000000000000000111110" 
        );

        checkBitVector(
            rd62,
            0xFF 
        );
        
        checkBitVector(
            rdm61,
            0xFF 
        );
    }

    @Test
    public void multiLayerMappingTests()
    {
        // TODO IMPLEMENT
        
    }
 
    @Test
    public void toByteArrayTests()
    {
        // TODO: MORE COMPLEX TESTS!!!
        
        final BitVector rd = BitVector.valueOf("01011100011010101");
        BigInteger bi = new BigInteger(rd.toByteArray());

        System.out.println(rd.toBinString());
        System.out.println(String.format("%" + rd.getBitSize() + "s", bi.toString(2)));
        
    }
    
    @Test
    public void toHexStringTests()
    {
        System.out.println(BitVector.valueOf("FFFF", 16, 16).toHexString());
        System.out.println(BitVector.valueOf("FFFF", 16, 16).toBinString());
        
        System.out.println(BitVector.valueOf(0xDEADBEEF, 32).toHexString());
    }

    @Test
    public void compareTo()
    {
        checkComparison(BitVector.valueOf("00000001"), BitVector.valueOf("10000000"), -1);
    }

    @Test
    public void bitExtractionTest()
    {
        boolean value = true;
        final BitVector bv = BitVector.valueOf("01010101010101010101");
        for (int i = 0; i < bv.getBitSize(); ++i)
        {
            Assert.assertTrue("Bit extracted doesn't match expected", value == bv.getBit(i));
            value = !value;
        }

    }
}
