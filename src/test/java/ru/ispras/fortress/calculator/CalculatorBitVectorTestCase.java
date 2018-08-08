/*
 * Copyright 2017-2018 ISP RAS (http://www.ispras.ru)
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

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.expression.StandardOperation;

import java.util.Arrays;
import java.util.Collection;

@RunWith(Parameterized.class)
public final class CalculatorBitVectorTestCase {
  @Parameterized.Parameter()
  public Enum<?> operationId;

  @Parameterized.Parameter(1)
  public Data expected;

  @Parameterized.Parameter(2)
  public Data[] operands;

  @Test
  public void test() {
    final Data actual = Calculator.calculate(operationId, operands);
    Assert.assertEquals(expected, actual);
  }

  private static Object[] newTestCase(
      final Enum<?> operationId,
      final Data expected,
      final Data... operands) {
    return new Object[] { operationId, expected, operands };
  }

  @Parameterized.Parameters(name = "{index}: {0}")
  public static Collection<Object[]> testCases() {
    return Arrays.asList(
        newTestCase(
            StandardOperation.BVAND,
            Data.newBitVector(0, 1),
            Data.newBitVector(1, 1),
            Data.newBitVector(0, 1)
        ),

        newTestCase(
            StandardOperation.BVOR,
            Data.newBitVector(1, 1),
            Data.newBitVector(1, 1),
            Data.newBitVector(0, 1)
        ),

        /*
        newTestCase(
            StandardOperation.BVAND,
            Data.newBitVector(0, 1),
            Data.newBitVector(1, 1),
            Data.newBoolean(false)
        ),

        newTestCase(
            StandardOperation.BVOR,
            Data.newBitVector(1, 1),
            Data.newBitVector(1, 1),
            Data.newBoolean(false)
        ),
        */

        newTestCase(
            StandardOperation.BVCONCAT,
            Data.newBitVector(0xDEADBEEF, 32),
            Data.newBitVector(0xDEAD, 16),
            Data.newBitVector(0xBEEF, 16)
        )
    );
  }
}
