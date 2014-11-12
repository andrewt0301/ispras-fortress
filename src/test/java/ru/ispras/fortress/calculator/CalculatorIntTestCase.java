/*
 * Copyright 2014 ISP RAS (http://www.ispras.ru)
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

import static org.junit.Assert.*;

import java.math.BigInteger;

import org.junit.Test;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.expression.StandardOperation;

public final class CalculatorIntTestCase {
  public static Data calculate(Enum<?> operationId, Data... operands) {
    return Calculator.calculate(operationId, operands);
  }

  public static void testEquals(Data expected, Enum<?> operationId, Data... operands) {
    assertEquals(expected, calculate(operationId, operands));
  }

  @Test
  public void testPLUSOperation() {
    testEquals(Data.newInteger(0), StandardOperation.PLUS, Data.newInteger(0));

    testEquals(Data.newInteger(1), StandardOperation.PLUS, Data.newInteger(1));
    testEquals(Data.newInteger(-1), StandardOperation.PLUS, Data.newInteger(-1));

    testEquals(Data.newInteger(Long.MIN_VALUE),
      StandardOperation.PLUS, Data.newInteger(Long.MIN_VALUE));
    testEquals(Data.newInteger(Long.MAX_VALUE),
      StandardOperation.PLUS, Data.newInteger(Long.MAX_VALUE));
  }

  @Test
  public void testMINUSOperation() {
    testEquals(Data.newInteger(0), StandardOperation.MINUS, Data.newInteger(0));

    testEquals(Data.newInteger(1), StandardOperation.MINUS, Data.newInteger(-1));
    testEquals(Data.newInteger(-1), StandardOperation.MINUS, Data.newInteger(1));

    testEquals(Data.newInteger(BigInteger.valueOf(Long.MIN_VALUE).negate()),
      StandardOperation.MINUS, Data.newInteger(Long.MIN_VALUE));

    testEquals(Data.newInteger(BigInteger.valueOf(Long.MAX_VALUE).negate()),
      StandardOperation.MINUS, Data.newInteger(Long.MAX_VALUE));
  }

  @Test
  public void testADDOperation() {
    testEquals(Data.newInteger(0), StandardOperation.ADD, Data.newInteger(0), Data.newInteger(0));
    testEquals(Data.newInteger(0), StandardOperation.ADD, Data.newInteger(1), Data.newInteger(-1));

    testEquals(Data.newInteger(-1),
      StandardOperation.ADD, Data.newInteger(Integer.MAX_VALUE), Data.newInteger(Integer.MIN_VALUE));

    testEquals(
      Data.newInteger(BigInteger.valueOf(Integer.MAX_VALUE).multiply(BigInteger.valueOf(2))),
      StandardOperation.ADD, Data.newInteger(Integer.MAX_VALUE), Data.newInteger(Integer.MAX_VALUE));
  }

  @Test
  public void testSUBOperation() {
    testEquals(Data.newInteger(0), StandardOperation.SUB, Data.newInteger(0), Data.newInteger(0));
    testEquals(Data.newInteger(2), StandardOperation.SUB, Data.newInteger(1), Data.newInteger(-1));

    testEquals(Data.newInteger(0),
      StandardOperation.SUB, Data.newInteger(Integer.MIN_VALUE), Data.newInteger(Integer.MIN_VALUE));

    testEquals(
      Data.newInteger(BigInteger.valueOf(Integer.MAX_VALUE).multiply(BigInteger.valueOf(2)).add(BigInteger.ONE)),
      StandardOperation.SUB, Data.newInteger(Integer.MAX_VALUE), Data.newInteger(Integer.MIN_VALUE));
  }

  @Test
  public void testMULOperation() {
    testEquals(Data.newInteger(0),  StandardOperation.MUL, Data.newInteger(0), Data.newInteger(0));
    testEquals(Data.newInteger(-1), StandardOperation.MUL, Data.newInteger(1), Data.newInteger(-1));
    testEquals(Data.newInteger(-1), StandardOperation.MUL, Data.newInteger(1), Data.newInteger(-1));

    testEquals(Data.newInteger(1),
      StandardOperation.MUL, Data.newInteger(1), Data.newInteger(-1), Data.newInteger(-1));

    testEquals(Data.newInteger(4),
      StandardOperation.MUL, Data.newInteger(2), Data.newInteger(2));

    testEquals(Data.newInteger(BigInteger.valueOf(Long.MIN_VALUE).multiply(BigInteger.valueOf(2))),
      StandardOperation.MUL, Data.newInteger(Long.MIN_VALUE), Data.newInteger(2));

    testEquals(Data.newInteger(BigInteger.valueOf(Long.MAX_VALUE).multiply(BigInteger.valueOf(2))),
      StandardOperation.MUL, Data.newInteger(Long.MAX_VALUE), Data.newInteger(2));
  }

  @Test
  public void testDIVOperation() {
    testEquals(Data.newInteger(0),
      StandardOperation.DIV, Data.newInteger(0), Data.newInteger(1));

    testEquals(Data.newInteger(256),
      StandardOperation.DIV, Data.newInteger(1024), Data.newInteger(4));

    testEquals(Data.newInteger(102),
      StandardOperation.DIV, Data.newInteger(1024), Data.newInteger(10));

    testEquals(Data.newInteger(1),
      StandardOperation.DIV, Data.newInteger(Long.MAX_VALUE), Data.newInteger(Long.MAX_VALUE));
  }

  @Test
  public void testREMOperation() {
    testEquals(Data.newInteger(2),  StandardOperation.REM, Data.newInteger(27),  Data.newInteger(5));
    testEquals(Data.newInteger(2),  StandardOperation.REM, Data.newInteger(-27), Data.newInteger(5));
    testEquals(Data.newInteger(-2), StandardOperation.REM, Data.newInteger(27),  Data.newInteger(-5));
    testEquals(Data.newInteger(-2), StandardOperation.REM, Data.newInteger(-27), Data.newInteger(-5));
  }

  @Test
  public void testMODOperation() {
    testEquals(Data.newInteger(2), StandardOperation.MOD, Data.newInteger(27),  Data.newInteger(5));
    testEquals(Data.newInteger(3), StandardOperation.MOD, Data.newInteger(-27), Data.newInteger(5));
    testEquals(Data.newInteger(2), StandardOperation.MOD, Data.newInteger(27),  Data.newInteger(-5));
    testEquals(Data.newInteger(3), StandardOperation.MOD, Data.newInteger(-27), Data.newInteger(-5));
  }
}
