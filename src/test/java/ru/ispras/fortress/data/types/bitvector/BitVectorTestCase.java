/*
 * Copyright 2012-2018 ISP RAS (http://www.ispras.ru)
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software distributed under the License
 * is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
 * or implied. See the License for the specific language governing permissions and limitations under
 * the License.
 */

package ru.ispras.fortress.data.types.bitvector;

import org.junit.Assert;
import org.junit.Test;

import java.math.BigInteger;

public class BitVectorTestCase {
  @Test
  public void creationTests() {
    TestUtils.header("Tests for the createEmpty and valueOf methods.");

    // ///////////////////////////////////////////////////////////////////////////////////
    // Tests for createEmpty(int bitSize)

    TestUtils.checkBitVector(BitVector.newEmpty(11), "00000000000");

    // ///////////////////////////////////////////////////////////////////////////////////
    // Tests for valueOf(final int value, final int bitSize)

    TestUtils.checkBitVector(BitVector.valueOf(1, 1), 1);
    TestUtils.checkBitVector(BitVector.valueOf(0, 1), "0");

    TestUtils.checkBitVector(BitVector.valueOf(-1, 32), -1);
    TestUtils.checkBitVector(BitVector.valueOf(-1, 7), "1111111");

    TestUtils.checkBitVector(BitVector.valueOf(0, 4), 0);
    TestUtils.checkBitVector(BitVector.valueOf(0, 33), 0);
    TestUtils.checkBitVector(BitVector.valueOf(-1, 35), -1);

    {
      final String binStr = "1110111";
      TestUtils.checkBitVector(
          BitVector.valueOf(Integer.valueOf(binStr, 2), binStr.length()), binStr);
    }

    {
      final String binStr = "1100101010011";
      TestUtils.checkBitVector(
          BitVector.valueOf(Integer.valueOf(binStr, 2), binStr.length()), binStr);
    }

    // ///////////////////////////////////////////////////////////////////////////////////
    // Tests for valueOf(final long value, final int bitSize)

    TestUtils.checkBitVector(BitVector.valueOf(0xFFFFL, 64), 0xFFFFL);
    TestUtils.checkBitVector(BitVector.valueOf(0xFFFF0000L, 64), 0xFFFF0000L);

    TestUtils.checkBitVector(BitVector.valueOf(0xFFFF0000FFFF0000L, 65), 0xFFFF0000FFFF0000L);

    // ///////////////////////////////////////////////////////////////////////////////////
    // Tests for valueOf(final String bs, final int bitSize) and valueOf(final String bs)

    TestUtils.checkBitVector(BitVector.valueOf("0101010011100110000"), "0101010011100110000");
    TestUtils.checkBitVector(BitVector.valueOf("1101010011100110001"), "1101010011100110001");

    TestUtils.checkBitVector(BitVector.valueOf("11111", 2, 8), "00011111");
    TestUtils.checkBitVector(BitVector.valueOf("11111", 2, 9), "000011111");

    TestUtils.checkBitVector(BitVector.valueOf("111011", 2, 8), "00111011");
    TestUtils.checkBitVector(BitVector.valueOf("11111111111011", 2, 9), "111111011");
  }

  // //////////////////////////////////////////////////////////////////////////////////
  // COPY CONSTRUCTOR, ASSIGN AND RESET TESTS
  // //////////////////////////////////////////////////////////////////////////////////

  @Test
  public void copyingTests() {
    // Some representative test data (with odd length).
    final String sample_35bit = "101" + "10101010" + "10101010" + "10101010" + "10101010";

    TestUtils.header("Copying Tests");

    // ////////////////////////////////////////////////////////
    // Test case 0: creates an empty data array and assigns data to it.

    final BitVector rd01 = BitVector.newEmpty(35);

    TestUtils.checkBitVector(rd01, 0);

    final BitVector rd02 = BitVector.valueOf(Long.valueOf(sample_35bit, 2), 35);

    TestUtils.checkBitVector(rd02, sample_35bit);

    rd01.assign(rd02);

    TestUtils.checkBitVector(rd01, sample_35bit);

    TestUtils.checkBitVector(rd02, sample_35bit);

    // We call reset to make sure we deal with a copy of the data.
    rd02.reset();

    TestUtils.checkBitVector(rd02, 0);

    TestUtils.checkBitVector(rd01, sample_35bit);

    // In this test case, we call reset to make sure we deal with a copy of the data.
    rd01.reset();

    TestUtils.checkBitVector(rd01, 0);

    // ////////////////////////////////////////////////////////
    // Test case 1: the assign and reset methods

    final BitVector rd11 = BitVector.valueOf(Long.valueOf(sample_35bit, 2), 35);
    final BitVector rd12 = BitVector.valueOf(Long.valueOf("11111111111111111", 2), 35);

    rd11.assign(rd12);

    TestUtils.checkBitVector(rd12, "00000000000000000011111111111111111");

    // We call reset to make sure we deal with a copy of the data.
    rd12.reset();

    TestUtils.checkBitVector(rd11, "00000000000000000011111111111111111");

    TestUtils.checkBitVector(rd12, 0);

    // In this test case, we call reset to make sure we deal with a copy of the data.
    rd11.reset();

    TestUtils.checkBitVector(rd11, 0);

    // ////////////////////////////////////////////////////////
    // Test case 2: the copy constructor

    final BitVector rd21 = BitVector.valueOf(Long.valueOf(sample_35bit, 2), 35);
    final BitVector rd22 = BitVector.copyOf(rd21);

    TestUtils.checkBitVector(rd21, sample_35bit);

    TestUtils.checkBitVector(rd22, sample_35bit);

    // We call reset to make sure we deal with a copy of the data.
    rd21.reset();

    TestUtils.checkBitVector(rd21, 0);

    TestUtils.checkBitVector(rd22, sample_35bit);

    // We call reset to make sure we deal with a copy of the data.
    rd22.reset();

    TestUtils.checkBitVector(rd21, 0);

    TestUtils.checkBitVector(rd22, 0);

    // ////////////////////////////////////////////////////////
    // Test case 3: assignment with truncation

    // NOTE: NO IMPLICIT CONVERSIONS ARE ALLOWED.
    // TO MAKE OPERATIONS IWTH DIFFERENT TYPES, WE NEED TO COERCE THEN EXPLICITLY.

    /*
     * final RawData rd31 = new RawDataStore(27);
     *
     * checkRawData( rd31, 0 );
     *
     * final RawData rd32 = new Int(Long.valueOf(SAMPLE_35BIT, 2), 35).getRawData();
     *
     * checkRawData( rd32, SAMPLE_35BIT );
     *
     * rd31.assign(rd32);
     *
     * checkRawData( rd31, "010"+"10101010"+"10101010"+"10101010" );
     *
     * checkRawData( rd32, SAMPLE_35BIT );
     */
  }

  @Test
  public void repeatTests() {
    TestUtils.header("Repeat tests");

    TestUtils.checkBitVector(BitVector.valueOf("101").repeat(3), "101101101");
    TestUtils.checkBitVector(BitVector.valueOf("10100").repeat(3), "101001010010100");
    TestUtils.checkBitVector(BitVector.valueOf(0xBE, 8).repeat(2), 0xBEBE);
    TestUtils.checkBitVector(BitVector.valueOf(0xBEEF, 16).repeat(2), 0xBEEFBEEF);
    TestUtils.checkBitVector(BitVector.valueOf(0xDEADBEEF, 32).repeat(2), 0xDEADBEEFDEADBEEFL);

    final BitVector bvSource = BitVector.valueOf(0xDEADBEEF, 32);
    final BitVector bvCopy = bvSource.repeat(2);

    TestUtils.checkBitVector(bvSource, 0xDEADBEEF);
    TestUtils.checkBitVector(bvCopy, 0xDEADBEEFDEADBEEFL);

    bvCopy.field(16, 47).assign(BitVector.valueOf(0xBAADF00D, 32));

    TestUtils.checkBitVector(bvCopy, 0xDEADBAADF00DBEEFL);
    TestUtils.checkBitVector(bvSource, 0xDEADBEEF);
  }

  // //////////////////////////////////////////////////////////////////////////////////
  // READING MAPPING TESTS
  // //////////////////////////////////////////////////////////////////////////////////

  @Test
  public void mappingReadingTests() {
    TestUtils.header("Mapping Reading Tests");

    // Some representative test data (with odd length).
    final String sample35bitBinStr = "101" + "10101010" + "10101010" + "10101010" + "10101010";

    TestUtils.trace(BitVector.valueOf(0xFF, 32).toBinString());
    TestUtils.trace(BitVector.valueOf(0xFF00FF00, 32).toBinString());

    TestUtils.checkBitVector(BitVector.newMapping(BitVector.valueOf(-1, 32), 0, 32), -1);

    TestUtils.checkBitVector(
        BitVector.newMapping(BitVector.valueOf(0xFF00FF00, 32), 0, 32), 0xFF00FF00);

    // NOT ALLOWED (ASSERTION)
    /*
     * checkRawData( BitVector.createMapping(BitVector.valueOf(-1, 32), 0, 0), "" );
     */

    // //////////////////////////////////////////////////////////
    // Test for multiple of 8 data arrays (no incomplete bytes).

    TestUtils.checkBitVector(BitVector.newMapping(BitVector.valueOf(0xFF00FF00, 32), 0, 8), 0x00);

    TestUtils.checkBitVector(BitVector.newMapping(BitVector.valueOf(0xFF00FF00, 32), 8, 8), 0xFF);

    TestUtils.checkBitVector(BitVector.newMapping(BitVector.valueOf(0xFF00FF00, 32), 16, 8), 0x00);

    TestUtils.checkBitVector(BitVector.newMapping(BitVector.valueOf(0xFF00FF00, 32), 24, 8), 0xFF);


    TestUtils.checkBitVector(BitVector.newMapping(BitVector.valueOf(0xFF00FF00, 32), 4, 8), 0xF0);

    TestUtils.checkBitVector(BitVector.newMapping(BitVector.valueOf(0xFF00FF00, 32), 20, 8), 0xF0);

    TestUtils.checkBitVector(
        BitVector.newMapping(BitVector.valueOf(0xFF00FF00, 32), 4, 16), 0x0FF0);

    TestUtils.checkBitVector(
        BitVector.newMapping(BitVector.valueOf(0xFF00FF00, 32), 12, 16), 0xF00F);

    // //////////////////////////////////////////////////////////
    // Test for data arrays with an incomplete high byte (size is not multiple of 8)

    TestUtils.checkBitVector(BitVector.newMapping(BitVector.valueOf(-1L, 35), 0, 35), -1L);

    TestUtils.checkBitVector(BitVector.newMapping(
        BitVector.valueOf(Long.valueOf("11" + sample35bitBinStr, 2), 35), 0, 35),
        sample35bitBinStr);

    TestUtils.checkBitVector(
        BitVector.newMapping(BitVector.valueOf(Long.valueOf(sample35bitBinStr, 2), 35), 27, 8),
        "101" + "10101");

    TestUtils.checkBitVector(
        BitVector.newMapping(BitVector.valueOf(Long.valueOf(sample35bitBinStr, 2), 35), 24, 11),
        "101" + "10101010");

    TestUtils.checkBitVector(
        BitVector.newMapping(BitVector.valueOf(Long.valueOf(sample35bitBinStr, 2), 35), 23, 11),
        "01" + "101010101");

    TestUtils.checkBitVector(BitVector.newMapping(
        BitVector.valueOf(Long.valueOf("11" + sample35bitBinStr, 2), 35), 1, 5), "10101");

    TestUtils.checkBitVector(BitVector.newMapping(
        BitVector.valueOf(Long.valueOf("11" + sample35bitBinStr, 2), 35), 2, 15), "0"
        + "10101010" + "101010");

    TestUtils.checkBitVector(BitVector.newMapping(
        BitVector.valueOf(Long.valueOf("11" + sample35bitBinStr, 2), 35), 8, 4), "1010");

    TestUtils.checkBitVector(BitVector.newMapping(BitVector.valueOf(0xFF00FF00, 29), 5, 23),
        "11110000000011111111000");

    TestUtils.checkBitVector(BitVector.newMapping(
        BitVector.valueOf(Long.valueOf("11" + sample35bitBinStr, 2), 35), 25, 10), "101"
        + "1010101");

    TestUtils.checkBitVector(
        BitVector.newMapping(BitVector.valueOf(0x00FFFFFF, 32), 22, 10), "0000000011");
  }

  // //////////////////////////////////////////////////////////////////////////////////
  // WRITING MAPPING TESTS
  // //////////////////////////////////////////////////////////////////////////////////

  @Test
  public void mappingWritingTests() {
    TestUtils.header("Mapping Writing Tests");

    // Some representative test data (with odd length).
    final String sample35BitBinStr = "101" + "10101010" + "10101010" + "10101010" + "10101010";



    // ////////////////////////////////////////////////////////
    // Test Case 1: Mapping size equals source size.

    final BitVector rd01 = BitVector.valueOf(Long.valueOf(sample35BitBinStr, 2), 35);

    TestUtils.checkBitVector(rd01, sample35BitBinStr);

    final BitVector rd02 = BitVector.valueOf(0xF0F00F, 35);

    TestUtils.checkBitVector(rd02, 0xF0F00F);

    final BitVector rdm01 = BitVector.newMapping(rd01, 0, rd01.getBitSize());

    TestUtils.checkBitVector(rdm01, sample35BitBinStr);

    rdm01.assign(rd02);

    TestUtils.checkBitVector(rd01, 0xF0F00F);

    TestUtils.checkBitVector(rd02, 0xF0F00F);

    TestUtils.checkBitVector(rdm01, 0xF0F00F);

    rd02.reset();

    TestUtils.checkBitVector(rd01, 0xF0F00F);

    TestUtils.checkBitVector(rd02, 0);

    TestUtils.checkBitVector(rdm01, 0xF0F00F);

    rdm01.reset();

    TestUtils.checkBitVector(rd01, 0);

    TestUtils.checkBitVector(rd02, 0);

    TestUtils.checkBitVector(rdm01, 0);

    // ////////////////////////////////////////////////////////
    // Test Case 2: Mapped region is located in the middle of the source data
    // array (the offset and the mapping length is multiple of 8).

    final BitVector rd11 = BitVector.valueOf(Long.valueOf(sample35BitBinStr, 2), 35);

    TestUtils.checkBitVector(rd11, sample35BitBinStr);

    final BitVector rd12 = BitVector.valueOf(0xFF, 8);

    TestUtils.checkBitVector(rd12, 0xFF);

    final BitVector rdm11 = BitVector.newMapping(rd11, 8, 8);

    TestUtils.checkBitVector(rdm11, "10101010");

    rdm11.assign(rd12);

    TestUtils.checkBitVector(rdm11, 0xFF);

    TestUtils.checkBitVector(rd11, "10110101010101010101111111110101010");

    // ////////////////////////////////////////////////////////
    // Test Case 3: Mapped region is located in the middle of the source data
    // array (the offset and the mapping length is multiple of 8).

    final BitVector rd31 = BitVector.valueOf(Long.valueOf(sample35BitBinStr, 2), 35);

    TestUtils.checkBitVector(rd31, sample35BitBinStr);

    final BitVector rd32 = BitVector.valueOf(0xFFFF, 11);

    TestUtils.checkBitVector(rd32, 0xFFFF);

    final BitVector rdm31 = BitVector.newMapping(rd31, 3, 11);

    TestUtils.checkBitVector(rdm31, "10101010101");

    rdm31.assign(rd32);

    TestUtils.checkBitVector(rd31, "10110101010101010101011111111111010");

    TestUtils.checkBitVector(rd32, "11111111111");

    TestUtils.checkBitVector(rdm31, 0xFFFF);

    rdm31.reset();

    TestUtils.checkBitVector(rd31, "10110101010101010101000000000000010");

    TestUtils.checkBitVector(rd32, "11111111111");

    TestUtils.checkBitVector(rdm31, 0);


    // ////////////////////////////////////////////////////////
    // Test Case 4: Mapped region is located in the middle of the source data
    // array (the offset is multiple of 8 and the mapping length is not multiple of 8).

    final BitVector rd41 = BitVector.valueOf(Long.valueOf(sample35BitBinStr, 2), 35);

    TestUtils.checkBitVector(rd41, sample35BitBinStr);

    final BitVector rd42 = BitVector.valueOf(0xFF, 5);

    TestUtils.checkBitVector(rd42, 0xFF);

    final BitVector rdm41 = BitVector.newMapping(rd41, 8, 5);

    TestUtils.checkBitVector(rdm41, "01010");

    rdm41.assign(rd42);

    TestUtils.checkBitVector(rd41, "10110101010101010101011111110101010");

    TestUtils.checkBitVector(rd42, "11111");

    TestUtils.checkBitVector(rdm41, "11111");

    /*
     * rdm31.reset();
     *
     * checkRawData( rd31, "10110101010101010101000000000000010" );
     *
     * checkRawData( rd32, "11111111111" );
     *
     * checkRawData( rdm31, 0 );
     */

    // ////////////////////////////////////////////////////////
    // Test Case 5: Mapped region is located in the middle of the source data
    // array (the offset is multiple of 8 and the mapping length is not multiple of 8).

    final BitVector rd51 = BitVector.valueOf(Long.valueOf(sample35BitBinStr, 2), 35);

    TestUtils.checkBitVector(rd51, sample35BitBinStr);

    final BitVector rd52 = BitVector.valueOf(0, 5);

    TestUtils.checkBitVector(rd52, 0);

    final BitVector rdm51 = BitVector.newMapping(rd51, 8, 5);

    TestUtils.checkBitVector(rdm51, "01010");

    rdm51.assign(rd52);

    TestUtils.checkBitVector(rd51, "10110101010101010101010000010101010");

    TestUtils.checkBitVector(rd52, 0);

    TestUtils.checkBitVector(rdm51, 0);

    // ////////////////////////////////////////////////////////
    // Test Case 6: Mapped region is located in the middle of the source data
    // array (the offset is multiple of 8 and the mapping length is not multiple of 8).

    final BitVector rd61 = BitVector.valueOf(0, 35);
    Assert.assertTrue(BitVector.valueOf("0101010011100110000").toBinString()
        .equals("0101010011100110000"));

    Assert.assertTrue(BitVector.valueOf("0101010011100110000").toBinString()
        .equals("0101010011100110000"));

    Assert.assertTrue(BitVector.valueOf("11111", 2, 8).toBinString().equals("00011111"));

    Assert.assertTrue(BitVector.valueOf("111011", 2, 8).toBinString().equals("00111011"));

    Assert.assertTrue(BitVector.valueOf("11111111111011", 2, 8).toBinString().equals("11111011"));
    TestUtils.checkBitVector(rd61, 0);

    final BitVector rd62 = BitVector.valueOf(0xFF, 5);

    TestUtils.checkBitVector(rd62, 0xFF);

    final BitVector rdm61 = BitVector.newMapping(rd61, 1, 5);

    TestUtils.checkBitVector(rdm61, "00000");

    rdm61.assign(rd62);

    TestUtils.checkBitVector(rd61, "00000000000000000000000000000111110");

    TestUtils.checkBitVector(rd62, 0xFF);

    TestUtils.checkBitVector(rdm61, 0xFF);
  }

  @Test
  public void multiLayerMappingTests() {
    // TODO IMPLEMENT

  }

  @Test
  public void toIntTests() {
    // Size == 32

    TestUtils.checkBitVector(BitVector.valueOf(0, 32), "00000000000000000000000000000000");
    Assert.assertEquals(0, BitVector.valueOf(0, 32).intValue());

    TestUtils.checkBitVector(BitVector.valueOf(-1, 32), "11111111111111111111111111111111");
    Assert.assertEquals(-1, BitVector.valueOf(-1, 32).intValue());

    TestUtils.checkBitVector(
        BitVector.valueOf(Integer.MIN_VALUE, 32), "10000000000000000000000000000000");
    Assert.assertEquals(Integer.MIN_VALUE, BitVector.valueOf(Integer.MIN_VALUE,  32).intValue());

    TestUtils.checkBitVector(
        BitVector.valueOf(Integer.MAX_VALUE, 32), "01111111111111111111111111111111");
    Assert.assertEquals(Integer.MAX_VALUE, BitVector.valueOf(Integer.MAX_VALUE,  32).intValue());

    // Size < 32 (16)

    TestUtils.checkBitVector(BitVector.valueOf(0, 16), "0000000000000000");
    Assert.assertEquals(0, BitVector.valueOf(0, 16).intValue());

    TestUtils.checkBitVector(BitVector.valueOf(-1, 16), "1111111111111111");
    Assert.assertEquals(0xFFFF, BitVector.valueOf(-1, 16).intValue());

    // Size > 32 (36)

    TestUtils.checkBitVector(BitVector.valueOf(0,  36), "000000000000000000000000000000000000");
    Assert.assertEquals(0, BitVector.valueOf(0, 36).intValue());

    TestUtils.checkBitVector(BitVector.valueOf(-1, 36), "000011111111111111111111111111111111");
    Assert.assertEquals(-1, BitVector.valueOf(-1, 36).intValue());
  }

  @Test
  public void toLongTests() {
    checkLongConversion(0);
    checkLongConversion(1);
    checkLongConversion(-1);

    checkLongConversion(0x00000000000000FFL);
    checkLongConversion(0x000000000000FF00L);
    checkLongConversion(0x0000000000FF0000L);
    checkLongConversion(0x00000000FF000000L);
    checkLongConversion(0x000000FF00000000L);
    checkLongConversion(0x0000FF0000000000L);
    checkLongConversion(0x00FF000000000000L);
    checkLongConversion(0xFF00000000000000L);

    checkLongConversion(0x00000000000A0000L);
    checkLongConversion(0xFFFFFFFFFFF5FFFFL);
    checkLongConversion(0xFFFFFFFFFFF5FFFFL);

    checkLongConversion(0xDEADBEEF);
    checkLongConversion(0xDEADBEEF00000000L);
    checkLongConversion(0xDEADBEEFBAADF00DL);
  }

  private void checkLongConversion(long value) {
    final BitVector bv = BitVector.valueOf(value, 64);
    System.out.println(bv.toHexString() + " must be == " + Long.toHexString(bv.longValue()));
    Assert.assertEquals(value, bv.longValue());
  }

  @Test
  public void toBigIntegerTests() {
    for (int bitSize = 1; bitSize <= 32; ++bitSize) {
      System.out.println(bitSize + ":");
      checkBigIntegerConversion(-1, bitSize);
      checkBigIntegerConversion(0,  bitSize);
    }

    for (int bitSize = 33; bitSize <= 64; ++bitSize) {
      System.out.println(bitSize + ":");
      checkBigIntegerConversion(-1L, bitSize);
      checkBigIntegerConversion(0L,  bitSize);
    }

    final BitVector bv0 = BitVector.valueOf(BigInteger.valueOf(0), 32);
    Assert.assertEquals("0", bv0.toHexString());
    Assert.assertEquals(BigInteger.valueOf(0), bv0.bigIntegerValue());

    final BitVector bv1 = BitVector.valueOf(BigInteger.valueOf(-1), 32);
    Assert.assertEquals("FFFFFFFF", bv1.toHexString());
    Assert.assertEquals(BigInteger.valueOf(-1), bv1.bigIntegerValue());

    final BitVector bv11 = BitVector.valueOf(BigInteger.valueOf(-1), 64);
    Assert.assertEquals("FFFFFFFFFFFFFFFF", bv11.toHexString());
    Assert.assertEquals(BigInteger.valueOf(-1), bv11.bigIntegerValue());

    final BitVector bv12 = BitVector.valueOf(new BigInteger("FFFFFFFFFFFFFFFF", 16), 64);
    Assert.assertEquals("FFFFFFFFFFFFFFFF", bv12.toHexString());
    Assert.assertEquals(BigInteger.valueOf(-1), bv12.bigIntegerValue());

    // Truncating BigInteger (1 becomes the highest bit - sign extension)
    final BitVector bv110 = BitVector.valueOf(new BigInteger("DEADBEEF", 16), 16);
    Assert.assertEquals("BEEF", bv110.toHexString());
    Assert.assertEquals(BigInteger.valueOf(0xFFFFBEEF), bv110.bigIntegerValue());

    // Truncating BigInteger (0 becomes the highest bit - no sign extension)
    final BitVector bv111 = BitVector.valueOf(new BigInteger("DEAD7EEF", 16), 16);
    Assert.assertEquals("7EEF", bv111.toHexString());
    Assert.assertEquals(BigInteger.valueOf(0x7EEF), bv111.bigIntegerValue());

    final BitVector bv2 = BitVector.valueOf(BigInteger.valueOf(1), 32);
    Assert.assertEquals("1", bv2.toHexString());
    Assert.assertEquals(BigInteger.valueOf(1), bv2.bigIntegerValue());

    final BitVector bv3 = BitVector.valueOf(BigInteger.valueOf(Integer.MAX_VALUE), 32);
    Assert.assertEquals("7FFFFFFF", bv3.toHexString());
    Assert.assertEquals(BigInteger.valueOf(Integer.MAX_VALUE), bv3.bigIntegerValue());

    final BitVector bv4 = BitVector.valueOf(BigInteger.valueOf(Integer.MIN_VALUE), 32);
    Assert.assertEquals("80000000", bv4.toHexString());
    Assert.assertEquals(BigInteger.valueOf(Integer.MIN_VALUE), bv4.bigIntegerValue());

    final BitVector bv5 = BitVector.valueOf(BigInteger.valueOf(Long.MAX_VALUE), Long.SIZE);
    Assert.assertEquals("7FFFFFFFFFFFFFFF", bv5.toHexString());
    Assert.assertEquals(BigInteger.valueOf(Long.MAX_VALUE), bv5.bigIntegerValue());

    final BitVector bv6 = BitVector.valueOf(BigInteger.valueOf(Long.MIN_VALUE), Long.SIZE);
    Assert.assertEquals("8000000000000000", bv6.toHexString());
    Assert.assertEquals(BigInteger.valueOf(Long.MIN_VALUE), bv6.bigIntegerValue());
  }

  private void checkBigIntegerConversion(int value, int bitSize) {
    final BitVector bv = BitVector.valueOf(value, bitSize);
    final BigInteger bi = BigInteger.valueOf(value);

    System.out.println(bv.toBinString());
    System.out.println(bi.toString(2));

    Assert.assertEquals(bi, bv.bigIntegerValue());
  }

  private void checkBigIntegerConversion(long value, int bitSize) {
    final BitVector bv = BitVector.valueOf(value, bitSize);
    final BigInteger bi = BigInteger.valueOf(value);

    System.out.println(bv.toBinString());
    System.out.println(bi.toString(2));

    Assert.assertEquals(bi, bv.bigIntegerValue());
  }

  @Test
  public void toByteArrayTests() {
    final byte[] byte_array = new byte[] {1, 2, 3, 4};

    final BitVector bv = BitVector.valueOf(byte_array, 32);
    System.out.println(bv.toHexString());

    for (int i = 0; i < byte_array.length; i++) {
      Assert.assertTrue(byte_array[i] == bv.getByte(i));
    }

    final byte[] bv_byte_array = bv.toByteArray();
    System.out.println(BitVector.valueOf(bv_byte_array, 32).toHexString());

    for (int i = 0; i < byte_array.length; i++) {
      Assert.assertTrue(byte_array[i] == bv_byte_array[i]);
    }

    Assert.assertEquals(
        "100000000110000001000000001",
        BitVector.valueOf(byte_array, 27).toString()
    );

    Assert.assertEquals(
        "00000100000000110000001000000001",
        BitVector.valueOf(byte_array, 32).toString()
    );

    Assert.assertEquals(
        "000000000000100000000110000001000000001",
        BitVector.valueOf(byte_array, 39).toString()
    );

    // TODO: MORE COMPLEX TESTS!!!
  }

  @Test
  public void toStringTests() {
    Assert.assertEquals("FFFF", BitVector.valueOf("FFFF", 16, 16).toHexString());
    Assert.assertEquals("1111111111111111", BitVector.valueOf("FFFF", 16, 16).toBinString());
    Assert.assertEquals("1111111111111111", BitVector.valueOf("FFFF", 16, 16).toString());

    Assert.assertEquals("FFFF", BitVector.valueOf("FFFF", 16, 32).toHexString());
    Assert.assertEquals("00000000000000001111111111111111",
        BitVector.valueOf("FFFF", 16, 32).toBinString());

    Assert.assertEquals("DEADBEEF", BitVector.valueOf(0xDEADBEEF, 32).toHexString());
  }

  @Test
  public void compareTo() {
    TestUtils.checkComparison(BitVector.valueOf("00000001"), BitVector.valueOf("10000000"), -1);
    TestUtils.checkComparison(BitVector.valueOf("10000000"), BitVector.valueOf("00000001"), 1);
    TestUtils.checkComparison(BitVector.valueOf("10000000"), BitVector.valueOf("10000000"), 0);
  }

  @Test
  public void bitExtractionTest() {
    boolean value = true;
    final BitVector bv = BitVector.valueOf("01010101010101010101");
    for (int i = 0; i < bv.getBitSize(); ++i) {
      Assert.assertTrue("Bit extracted doesn't match expected", value == bv.getBit(i));
      value = !value;
    }
  }

  @Test
  public void bitSetTest() {
    testSetBit(BitVector.valueOf("111"), 1, true);
    testSetBit(BitVector.valueOf("111"), 1, false);

    testSetBit(BitVector.valueOf("100100111"), 1, true);
    testSetBit(BitVector.valueOf("100100111"), 1, false);
    testSetBit(BitVector.valueOf("100100111"), 8, true);
    testSetBit(BitVector.valueOf("100100111"), 8, false);

    testSetBit(BitVector.valueOf(0xFFFFFFFF, 32), 0, true);
    testSetBit(BitVector.valueOf(0xFFFFFFFF, 32), 0, false);
    testSetBit(BitVector.valueOf(0xFFFFFFFF, 32), 31, true);
    testSetBit(BitVector.valueOf(0xFFFFFFFF, 32), 31, false);
    testSetBit(BitVector.valueOf(0xFFFFFFFF, 32), 20, true);
    testSetBit(BitVector.valueOf(0xFFFFFFFF, 32), 20, false);

    testSetBit(BitVector.valueOf(0x0, 32), 10, true);
    testSetBit(BitVector.valueOf(0xDEADBEEF, 32), 10, false);

    testSetBit(BitVector.valueOf("111"));
    testSetBit(BitVector.valueOf("100100111"));
    testSetBit(BitVector.valueOf("01010101010101010101"));
    testSetBit(BitVector.valueOf(0xFFFFFFFF, 32));
    testSetBit(BitVector.valueOf(0x0, 32));
    testSetBit(BitVector.valueOf(0xDEADBEEF, 32));
  }

  @Test
  public void fieldTest() {
    final BitVector bv = BitVector.valueOf(0xDEADBEEFBAADF00DL, 64);
    final BitVector bvField = bv.field(16, 47);

    Assert.assertEquals(BitVector.valueOf(0xBEEFBAAD, 32), bvField);
    bvField.assign(BitVector.valueOf(0xBAADBEEF, 32));

    Assert.assertEquals(BitVector.valueOf(0xBAADBEEF, 32), bvField);
    Assert.assertEquals(BitVector.valueOf(0xDEADBAADBEEFF00DL, 64), bv);
  }

  @Test
  public void resizeTest() {
    final BitVector bv1 = BitVector.valueOf(0x1, 32);
    final BitVector bv2 = BitVector.valueOf(0xFFFFFFFF, 32);
    final BitVector bv3 = BitVector.valueOf(0xFFFFFFF, 32);
    final BitVector bv4 = BitVector.valueOf(0xDEADBEEF, 32);

    Assert.assertEquals(BitVector.valueOf(0x1, 16), bv1.resize(16, false));
    Assert.assertEquals(BitVector.valueOf(0x1, 16), bv1.resize(16, true));
    Assert.assertEquals(BitVector.valueOf(0x1, 32), bv1.resize(32, false));
    Assert.assertEquals(BitVector.valueOf(0x1, 32), bv1.resize(32, true));
    Assert.assertEquals(BitVector.valueOf(0x1, 64), bv1.resize(64, false));
    Assert.assertEquals(BitVector.valueOf(0x1, 64), bv1.resize(64, true));

    Assert.assertEquals(BitVector.valueOf(0xFFFF, 16), bv2.resize(16, false));
    Assert.assertEquals(BitVector.valueOf(0xFFFF, 16), bv2.resize(16, true));
    Assert.assertEquals(BitVector.valueOf(0xFFFFFFFF, 32), bv2.resize(32, false));
    Assert.assertEquals(BitVector.valueOf(0xFFFFFFFF, 32), bv2.resize(32, true));
    Assert.assertEquals(BitVector.valueOf(0x00000000FFFFFFFFL, 64), bv2.resize(64, false));
    Assert.assertEquals(BitVector.valueOf(0xFFFFFFFFFFFFFFFFL, 64), bv2.resize(64, true));

    Assert.assertEquals(BitVector.valueOf(0xFFFF, 16), bv3.resize(16, false));
    Assert.assertEquals(BitVector.valueOf(0xFFFF, 16), bv3.resize(16, true));
    Assert.assertEquals(BitVector.valueOf(0xFFFFFFF, 32), bv3.resize(32, false));
    Assert.assertEquals(BitVector.valueOf(0xFFFFFFF, 32), bv3.resize(32, true));
    Assert.assertEquals(BitVector.valueOf(0x000000000FFFFFFFL, 64), bv3.resize(64, false));
    Assert.assertEquals(BitVector.valueOf(0x000000000FFFFFFFL, 64), bv3.resize(64, true));

    Assert.assertEquals(BitVector.valueOf(0xBEEF, 16), bv4.resize(16, false));
    Assert.assertEquals(BitVector.valueOf(0xBEEF, 16), bv4.resize(16, true));
    Assert.assertEquals(BitVector.valueOf(0xDEADBEEF, 32), bv4.resize(32, false));
    Assert.assertEquals(BitVector.valueOf(0xDEADBEEF, 32), bv4.resize(32, true));
    Assert.assertEquals(BitVector.valueOf(0x00000000DEADBEEFL, 64), bv4.resize(64, false));
    Assert.assertEquals(BitVector.valueOf(0xFFFFFFFFDEADBEEFL, 64), bv4.resize(64, true));
  }

  @Test
  public void setResetTest() {
    Assert.assertTrue(BitVector.valueOf(-1L, 64).isAllSet());
    Assert.assertFalse(BitVector.valueOf(-1L, 64).isAllReset());

    Assert.assertFalse(BitVector.valueOf(0, 64).isAllSet());
    Assert.assertTrue(BitVector.valueOf(0, 64).isAllReset());

    Assert.assertFalse(BitVector.valueOf(0xDEADBEEF, 32).isAllSet());
    Assert.assertFalse(BitVector.valueOf(0xDEADBEEF, 32).isAllReset());

    final BitVector bv1 = BitVector.valueOf(-1L, 64);
    Assert.assertTrue(bv1.isAllSet());
    bv1.reset();
    Assert.assertTrue(bv1.isAllReset());
    bv1.setAll();
    Assert.assertTrue(bv1.isAllSet());

    final BitVector bv2 = BitVector.valueOf(0xDEADFFFFFFFFBEEFL, 64);
    final BitVector bv2Mask1 = BitVector.newMapping(bv2, 0, 16);
    final BitVector bv2Mask2 = BitVector.newMapping(bv2, 16, 32);
    final BitVector bv2Mask3 = BitVector.newMapping(bv2, 48, 16);

    Assert.assertFalse(bv2Mask1.isAllSet());
    Assert.assertFalse(bv2Mask1.isAllReset());
    Assert.assertTrue(bv2Mask2.isAllSet());
    Assert.assertFalse(bv2Mask3.isAllSet());
    Assert.assertFalse(bv2Mask3.isAllReset());

    bv2Mask1.setAll();
    bv2Mask3.setAll();
    Assert.assertTrue(bv2.isAllSet());

    bv2Mask1.reset();
    bv2Mask3.reset();
    Assert.assertFalse(bv2.isAllSet());

    bv2Mask2.reset();
    Assert.assertTrue(bv2.isAllReset());
  }

  private static void testSetBit(final BitVector bv, final int index, final boolean value) {
    //System.out.println(bv);
    bv.setBit(index, value);
    //System.out.println(bv);
    Assert.assertEquals(value, bv.getBit(index));
  }

  private static void testSetBit(final BitVector bv) {
    final BitVector expected = BitVectorMath.not(bv.copy());

    final BitVector actual = bv.copy();
    for (int i = 0; i < bv.getBitSize(); ++i) {
      actual.setBit(i, !actual.getBit(i));
    }

    //System.out.println("~ " + bv + " : " + expected + " : " + actual);
    Assert.assertEquals(expected, actual);
  }
}
