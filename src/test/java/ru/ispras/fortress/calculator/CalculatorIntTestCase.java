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

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

@RunWith(Parameterized.class)
public final class CalculatorIntTestCase {
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

  private static Object[] newTestCase(
      final Enum<?> operationId,
      final int expected,
      final int... operands) {
    final Data[] dataOperands = new Data[operands.length];
    for (int index = 0; index < operands.length; ++index) {
      dataOperands[index] = Data.newInteger(operands[index]);
    }
    return newTestCase(operationId, Data.newInteger(expected), dataOperands);
  }

  private static Object[] newTestCase(
      final Enum<?> operationId,
      final long expected,
      final long... operands) {
    final Data[] dataOperands = new Data[operands.length];
    for (int index = 0; index < operands.length; ++index) {
      dataOperands[index] = Data.newInteger(operands[index]);
    }
    return newTestCase(operationId, Data.newInteger(expected), dataOperands);
  }

  @Parameterized.Parameters(name = "{index}: {0}")
  public static Collection<Object[]> testCases() {
    final List<Object[]> testCases = new ArrayList<>();

    testCases.addAll(newPlusTestCases());
    testCases.addAll(newMinusTestCases());
    testCases.addAll(newAddTestCases());
    testCases.addAll(newSubTestCases());
    testCases.addAll(newMulTestCases());
    testCases.addAll(newDivTestCases());
    testCases.addAll(newRemTestCases());
    testCases.addAll(newModTestCases());

    return testCases;
  }

  private static List<Object[]> newPlusTestCases() {
    return Arrays.asList(
        newTestCase(StandardOperation.PLUS, 0,  0),
        newTestCase(StandardOperation.PLUS, 1,  1),
        newTestCase(StandardOperation.PLUS, -1, -1),
        newTestCase(StandardOperation.PLUS, Long.MIN_VALUE, Long.MIN_VALUE),
        newTestCase(StandardOperation.PLUS, Long.MAX_VALUE, Long.MAX_VALUE)
    );
  }

  private static List<Object[]> newMinusTestCases() {
    return Arrays.asList(
        newTestCase(StandardOperation.MINUS, 0, 0),
        newTestCase(StandardOperation.MINUS, 1, -1),
        newTestCase(StandardOperation.MINUS, -1, 1),
        newTestCase(
            StandardOperation.MINUS,
            Data.newInteger(BigInteger.valueOf(Long.MIN_VALUE).negate()),
            Data.newInteger(Long.MIN_VALUE)
        ),
        newTestCase(
            StandardOperation.MINUS,
            Data.newInteger(BigInteger.valueOf(Long.MAX_VALUE).negate()),
            Data.newInteger(Long.MAX_VALUE)
        )
    );
  }

  private static List<Object[]> newAddTestCases() {
    return Arrays.asList(
        newTestCase(StandardOperation.ADD, 0, 0, 0),
        newTestCase(StandardOperation.ADD, 0, 1, -1),
        newTestCase(StandardOperation.ADD, -1, Integer.MAX_VALUE, Integer.MIN_VALUE),
        newTestCase(
            StandardOperation.ADD,
            Data.newInteger(BigInteger.valueOf(Integer.MAX_VALUE).multiply(BigInteger.valueOf(2))),
            Data.newInteger(Integer.MAX_VALUE), Data.newInteger(Integer.MAX_VALUE)
        )
    );
  }

  private static List<Object[]> newSubTestCases() {
    return Arrays.asList(
        newTestCase(StandardOperation.SUB, 0, 0, 0),
        newTestCase(StandardOperation.SUB, 2, 1, -1),
        newTestCase(StandardOperation.SUB, 0, Integer.MIN_VALUE, Integer.MIN_VALUE),
        newTestCase(
            StandardOperation.SUB,
            Data.newInteger(
                BigInteger.valueOf(Integer.MAX_VALUE)
                    .multiply(BigInteger.valueOf(2)).add(BigInteger.ONE)),
            Data.newInteger(Integer.MAX_VALUE),
            Data.newInteger(Integer.MIN_VALUE)
        )
    );
  }

  private static List<Object[]> newMulTestCases() {
    return Arrays.asList(
        newTestCase(StandardOperation.MUL, 0, 0, 0),
        newTestCase(StandardOperation.MUL, -1, 1, -1),
        newTestCase(StandardOperation.MUL, -1, 1, -1),
        newTestCase(StandardOperation.MUL, 1, 1, -1, -1),
        newTestCase(StandardOperation.MUL, 4, 2, 2),
        newTestCase(
            StandardOperation.MUL,
            Data.newInteger(BigInteger.valueOf(Long.MIN_VALUE).multiply(BigInteger.valueOf(2))),
            Data.newInteger(Long.MIN_VALUE),
            Data.newInteger(2)
        ),
        newTestCase(
            StandardOperation.MUL,
            Data.newInteger(BigInteger.valueOf(Long.MAX_VALUE).multiply(BigInteger.valueOf(2))),
            Data.newInteger(Long.MAX_VALUE),
            Data.newInteger(2)
        )
    );
  }

  private static List<Object[]> newDivTestCases() {
    return Arrays.asList(
        newTestCase(StandardOperation.DIV, 0, 0, 1),
        newTestCase(StandardOperation.DIV, 256, 1024, 4),
        newTestCase(StandardOperation.DIV, 102, 1024, 10),
        newTestCase(StandardOperation.DIV, 1, Long.MAX_VALUE, Long.MAX_VALUE)
    );
  }

  private static List<Object[]> newRemTestCases() {
    return Arrays.asList(
        newTestCase(StandardOperation.REM, 2, 27, 5),
        newTestCase(StandardOperation.REM, 2, -27, 5),
        newTestCase(StandardOperation.REM, -2, 27, -5),
        newTestCase(StandardOperation.REM, -2, -27, -5)
    );
  }

  private static List<Object[]> newModTestCases() {
    return Arrays.asList(
        newTestCase(StandardOperation.MOD, 2, 27, 5),
        newTestCase(StandardOperation.MOD, 3, -27, 5),
        newTestCase(StandardOperation.MOD, 2, 27, -5),
        newTestCase(StandardOperation.MOD, 3, -27, -5)
    );
  }
}
