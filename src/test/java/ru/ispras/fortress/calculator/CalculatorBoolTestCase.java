/*
 * Copyright 2014-2018 ISP RAS (http://www.ispras.ru)
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
public final class CalculatorBoolTestCase {
  private static final Data TRUE = Data.newBoolean(true);
  private static final Data FALSE = Data.newBoolean(false);

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
        newTestCase(StandardOperation.NOT, FALSE, TRUE),
        newTestCase(StandardOperation.NOT, TRUE,  FALSE),

        newTestCase(StandardOperation.AND, FALSE, FALSE, FALSE),
        newTestCase(StandardOperation.AND, FALSE, TRUE,  FALSE),
        newTestCase(StandardOperation.AND, FALSE, FALSE, TRUE),
        newTestCase(StandardOperation.AND, TRUE,  TRUE,  TRUE),

        newTestCase(StandardOperation.AND, TRUE,  TRUE,  TRUE,  TRUE),
        newTestCase(StandardOperation.AND, FALSE, TRUE,  TRUE,  FALSE),
        newTestCase(StandardOperation.AND, FALSE, TRUE,  FALSE, TRUE),
        newTestCase(StandardOperation.AND, FALSE, TRUE,  FALSE, FALSE),
        newTestCase(StandardOperation.AND, FALSE, FALSE, TRUE,  TRUE),
        newTestCase(StandardOperation.AND, FALSE, FALSE, TRUE,  FALSE),
        newTestCase(StandardOperation.AND, FALSE, FALSE, FALSE, TRUE),
        newTestCase(StandardOperation.AND, FALSE, FALSE, FALSE, FALSE),

        newTestCase(StandardOperation.OR,  FALSE, FALSE, FALSE),
        newTestCase(StandardOperation.OR,  TRUE,  TRUE,  FALSE),
        newTestCase(StandardOperation.OR,  TRUE,  FALSE, TRUE),
        newTestCase(StandardOperation.OR,  TRUE,  TRUE,  TRUE),

        newTestCase(StandardOperation.OR,  TRUE,  TRUE,  TRUE,  TRUE),
        newTestCase(StandardOperation.OR,  TRUE,  TRUE,  TRUE,  FALSE),
        newTestCase(StandardOperation.OR,  TRUE,  TRUE,  FALSE, TRUE),
        newTestCase(StandardOperation.OR,  TRUE,  TRUE,  FALSE, FALSE),
        newTestCase(StandardOperation.OR,  TRUE,  FALSE, TRUE,  TRUE),
        newTestCase(StandardOperation.OR,  TRUE,  FALSE, TRUE,  FALSE),
        newTestCase(StandardOperation.OR,  TRUE,  FALSE, FALSE, TRUE),
        newTestCase(StandardOperation.OR,  FALSE, FALSE, FALSE, FALSE),

        newTestCase(StandardOperation.XOR, FALSE, FALSE, FALSE),
        newTestCase(StandardOperation.XOR, TRUE,  TRUE,  FALSE),
        newTestCase(StandardOperation.XOR, TRUE,  FALSE, TRUE),
        newTestCase(StandardOperation.XOR, FALSE, TRUE,  TRUE),

        newTestCase(StandardOperation.XOR, TRUE,  TRUE,  TRUE,  TRUE),
        newTestCase(StandardOperation.XOR, FALSE, TRUE,  TRUE,  FALSE),
        newTestCase(StandardOperation.XOR, FALSE, TRUE,  FALSE, TRUE),
        newTestCase(StandardOperation.XOR, TRUE,  TRUE,  FALSE, FALSE),
        newTestCase(StandardOperation.XOR, FALSE, FALSE, TRUE,  TRUE),
        newTestCase(StandardOperation.XOR, TRUE,  FALSE, TRUE,  FALSE),
        newTestCase(StandardOperation.XOR, TRUE,  FALSE, FALSE, TRUE),
        newTestCase(StandardOperation.XOR, FALSE, FALSE, FALSE, FALSE),

        newTestCase(StandardOperation.IMPL, TRUE,  FALSE, FALSE),
        newTestCase(StandardOperation.IMPL, FALSE, TRUE,  FALSE),
        newTestCase(StandardOperation.IMPL, TRUE,  FALSE, TRUE),
        newTestCase(StandardOperation.IMPL, TRUE,  TRUE,  TRUE)
    );
  }
}
