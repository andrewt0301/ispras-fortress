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

package ru.ispras.fortress.calculator;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.expression.StandardOperation;

public final class CalculatorBitVectorTestCase {
  public static Data calculate(
      final Enum<?> operationId,
      final Data... operands) {
    return Calculator.calculate(operationId, operands);
  }

  public static void testEquals(
      final Data expected,
      final Enum<?> operationId,
      final Data... operands) {
    assertEquals(expected, calculate(operationId, operands));
  }

  @Test
  public void test() {
    testEquals(
        Data.newBitVector(0, 1),
        StandardOperation.BVAND, Data.newBitVector(1, 1), Data.newBitVector(0, 1)
        );

    testEquals(
        Data.newBitVector(1, 1),
        StandardOperation.BVOR, Data.newBitVector(1, 1), Data.newBitVector(0, 1)
        );
/*
    testEquals(
        Data.newBitVector(0, 1),
        StandardOperation.BVAND, Data.newBitVector(1, 1), Data.newBoolean(false)
        );

    testEquals(
        Data.newBitVector(1, 1),
        StandardOperation.BVOR, Data.newBitVector(1, 1), Data.newBoolean(false)
        );
*/
  }

  @Test
  public void testConcat() {
    testEquals(
        Data.newBitVector(0xDEADBEEF, 32),
        StandardOperation.BVCONCAT, Data.newBitVector(0xBEEF, 16), Data.newBitVector(0xDEAD, 16)
        );
  }
}
