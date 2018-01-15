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

import org.junit.Test;

public class BitVectorMultiMappingTestCase {
  @Test
  public void test1() {
    final BitVector rd1 = BitVector.valueOf("11110000");
    final BitVector rd2 = BitVector.valueOf("00110011");
    final BitVector rd3 = BitVector.valueOf("11000000");

    final BitVector rd = BitVector.newMapping(rd1, rd2, rd3);
    TestUtils.checkBitVector(rd, "11110000" + "00110011" + "11000000");

    rd.assign(BitVector.valueOf("11000011" + "11011011" + "10100001"));
    TestUtils.checkBitVector(rd, "11000011" + "11011011" + "10100001");

    TestUtils.checkBitVector(rd1, "11000011");
    TestUtils.checkBitVector(rd2, "11011011");
    TestUtils.checkBitVector(rd3, "10100001");
  }

  @Test
  public void test2() {
    final BitVector rd1 = BitVector.valueOf("0110");
    final BitVector rd2 = BitVector.valueOf("1001");

    final BitVector rd = BitVector.newMapping(rd1, rd2);
    TestUtils.checkBitVector(rd, "0110" + "1001");

    rd.assign(BitVector.valueOf("1111" + "0000"));

    TestUtils.checkBitVector(rd, "1111" + "0000");
    TestUtils.checkBitVector(rd1, "1111");
    TestUtils.checkBitVector(rd2, "0000");
  }

  @Test
  public void test21() {
    final BitVector rd1 = BitVector.valueOf("011");
    final BitVector rd2 = BitVector.valueOf("1001");

    final BitVector rd = BitVector.newMapping(rd1, rd2);
    TestUtils.checkBitVector(rd, "011" + "1001");

    final BitVector rdX = BitVector.valueOf("1111" + "000");
    TestUtils.checkBitVector(rdX, "1111" + "000");

    rd.assign(rdX);

    TestUtils.checkBitVector(rd, "1111" + "000");
    TestUtils.checkBitVector(rd1, "111");
    TestUtils.checkBitVector(rd2, "1000");
  }

  @Test
  public void test3() {
    final BitVector rd1 = BitVector.valueOf("0010000110");
    final BitVector rd2 = BitVector.valueOf("00001001");
    final BitVector rd = BitVector.newMapping(rd1, rd2);

    System.out.println(rd.toBinString());
    TestUtils.checkBitVector(rd, "0010000110" + "00001001");

    /*
     * rd.assign( RawData.valueOf("01010101" + "1100110011") );
     *
     * checkRawData( rd, "01010101" + "1100110011" );
     */

    final BitVector rdX = BitVector.valueOf("11110011" + "1111110011");
    rd.assign(rdX);

    TestUtils.checkBitVector(rd, "11110011" + "1111110011");
  }

  @Test
  public void test4() {
    final BitVector rd1 = BitVector.valueOf("1100000000");
    final BitVector rd2 = BitVector.valueOf("00");
    final BitVector rd3 = BitVector.valueOf("111");
    final BitVector rd4 = BitVector.valueOf("1100011100");
    final BitVector rd = BitVector.newMapping(rd1, rd2, rd3, rd4);

    System.out.println(rd.toBinString());
    TestUtils.checkBitVector(rd, "1100000000" + "00" + "111" + "1100011100");
  }

  @Test
  public void test5() {
    final BitVector rd1 = BitVector.valueOf("1");
    final BitVector rd2 = BitVector.valueOf("0");
    final BitVector rd3 = BitVector.valueOf("0");
    final BitVector rd4 = BitVector.valueOf("1");
    final BitVector rd5 = BitVector.valueOf("1");
    final BitVector rd = BitVector.newMapping(rd1, rd2, rd3, rd4, rd5);

    System.out.println(rd.toBinString());
    TestUtils.checkBitVector(rd, "10011");

    rd.assign(BitVector.valueOf("00110"));
    TestUtils.checkBitVector(rd, "00110");

    TestUtils.checkBitVector(rd1, "0");
    TestUtils.checkBitVector(rd2, "0");
    TestUtils.checkBitVector(rd3, "1");
    TestUtils.checkBitVector(rd4, "1");
    TestUtils.checkBitVector(rd5, "0");
  }

  @Test
  public void test6() {
    final BitVector rd1 = BitVector.valueOf("111100001");
    final BitVector rd2 = BitVector.valueOf("0000111100");
    final BitVector rd3 = BitVector.valueOf("00110110101");
    final BitVector rd4 = BitVector.valueOf("11110000");
    final BitVector rd5 = BitVector.valueOf("111");
    final BitVector rd = BitVector.newMapping(rd1, rd2, rd3, rd4, rd5);

    System.out.println(rd.toBinString());
    TestUtils.checkBitVector(rd, "111100001" + "0000111100" + "00110110101" + "11110000" + "111");
  }
}
