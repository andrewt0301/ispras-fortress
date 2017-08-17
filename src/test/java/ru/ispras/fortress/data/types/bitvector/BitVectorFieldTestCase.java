/*
 * Copyright 2017 ISP RAS (http://www.ispras.ru)
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

import ru.ispras.fortress.randomizer.Randomizer;

public final class BitVectorFieldTestCase {
  @Test
  public void test() {
    final int bitVectorSize = 64;
    for (int field1Size = 1; field1Size <= 32; field1Size++) {
      for (int field2Size = 1; field2Size <= 32; field2Size++) {
        int field1Min = field2Size;
        int field1Max = field1Min + field1Size - 1;

        while (field1Max < bitVectorSize) {
          final int field2Max = field1Min - 1;
          final int field2Min = field2Max - field2Size + 1;

          doTest(
              bitVectorSize,
              field1Size,
              field1Max,
              field1Min,
              field2Size,
              field2Max,
              field2Min
              );

          field1Min++;
          field1Max = field1Min + field1Size - 1;
        }
      }
    }
  }

  private void doTest(
      final int bitVectorSize,
      final int field1Size,
      final int field1Max,
      final int field1Min,
      final int field2Size,
      final int field2Max,
      final int field2Min) {
    //System.out.printf("%d: <%d..%d> || <%d..%d>%n",
    //    bitVectorSize, field1Max, field1Min, field2Max, field2Min);

    final BitVector value1 = BitVector.valueOf(-1L, field1Size);
    final BitVector value2 = BitVector.valueOf(-1L, field2Size);

    final BitVector bitVector = BitVector.newEmpty(bitVectorSize);
    final BitVector field1 = bitVector.field(field1Max, field1Min);
    final BitVector field2 = bitVector.field(field2Max, field2Min);

    field1.assign(value1);
    field2.assign(value2);

    TestUtils.checkBitVector(field1, value1);
    TestUtils.checkBitVector(field2, value2);
  }

  @Test
  public void test1() {
    final BitVector bitVector = BitVector.newEmpty(64);

    final int fieldPos = 12;
    final int fieldSize = 12;

    final BitVector field = BitVector.newMapping(bitVector, fieldPos, fieldSize);

    final BitVector value1 = BitVector.valueOf("010001001000");
    final BitVector value2 = BitVector.valueOf("010010011100");

    field.assign(value1);
    TestUtils.checkBitVector(field, value1);

    field.assign(value2);
    TestUtils.checkBitVector(field, value2);
  }

  @Test
  public void test2() {
    final int size = 64;
    final BitVector bitVector = BitVector.newEmpty(size);

    for (int fieldStartPos = 0; fieldStartPos < size; fieldStartPos++) {
      final int remainingSize = size - fieldStartPos + 1;
      for (int fieldSize = 1; fieldSize < remainingSize; fieldSize++) {
        final BitVector field = BitVector.newMapping(bitVector, fieldStartPos, fieldSize);
        final int fieldEndPos = fieldStartPos + fieldSize;

        final BitVector preField = fieldStartPos > 0 ?
            BitVector.newMapping(bitVector, 0, fieldStartPos) : null;

        final BitVector postField = fieldEndPos < size ?
            BitVector.newMapping(bitVector, fieldEndPos, size - fieldEndPos) : null;

        final BitVector preFieldCopy = null != preField ? preField.copy() : null;
        final BitVector postFieldCopy = null != postField ? postField.copy() : null;

        final BitVector value = BitVector.newEmpty(fieldSize);
        Randomizer.get().fill(value);

        field.assign(value);
        TestUtils.checkBitVector(field, value);

        if (null != preField) {
          TestUtils.checkBitVector(preField, preFieldCopy);
        }

        if (null != postField) {
          TestUtils.checkBitVector(postField, postFieldCopy);
        }
      }
    }
  }
}
