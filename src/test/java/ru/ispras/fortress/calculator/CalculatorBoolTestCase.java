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

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.expression.StandardOperation;

import org.junit.Assert;
import org.junit.Test;

public final class CalculatorBoolTestCase {
  private static final Data TRUE = Data.newBoolean(true);
  private static final Data FALSE = Data.newBoolean(false);

  public static boolean calculate(final Enum<?> operationId, final Data... operands) {
    final Data data = Calculator.calculate(operationId, operands);
    return ((Boolean) data.getValue()).booleanValue();
  }

  @Test
  public void testNotOperation() {
    Assert.assertFalse(calculate(StandardOperation.NOT, TRUE));
    Assert.assertTrue(calculate(StandardOperation.NOT, FALSE));
  }

  @Test
  public void testAndOperation() {
    Assert.assertFalse(calculate(StandardOperation.AND, FALSE, FALSE));
    Assert.assertFalse(calculate(StandardOperation.AND, TRUE, FALSE));
    Assert.assertFalse(calculate(StandardOperation.AND, FALSE, TRUE));
    Assert.assertTrue(calculate(StandardOperation.AND, TRUE, TRUE));

    Assert.assertTrue(calculate(StandardOperation.AND, TRUE, TRUE, TRUE));
    Assert.assertFalse(calculate(StandardOperation.AND, TRUE, TRUE, FALSE));
    Assert.assertFalse(calculate(StandardOperation.AND, TRUE, FALSE, TRUE));
    Assert.assertFalse(calculate(StandardOperation.AND, TRUE, FALSE, FALSE));
    Assert.assertFalse(calculate(StandardOperation.AND, FALSE, TRUE, TRUE));
    Assert.assertFalse(calculate(StandardOperation.AND, FALSE, TRUE, FALSE));
    Assert.assertFalse(calculate(StandardOperation.AND, FALSE, FALSE, TRUE));
    Assert.assertFalse(calculate(StandardOperation.AND, FALSE, FALSE, FALSE));
  }

  @Test
  public void testOrOperation() {
    Assert.assertFalse(calculate(StandardOperation.OR, FALSE, FALSE));
    Assert.assertTrue(calculate(StandardOperation.OR, TRUE, FALSE));
    Assert.assertTrue(calculate(StandardOperation.OR, FALSE, TRUE));
    Assert.assertTrue(calculate(StandardOperation.OR, TRUE, TRUE));

    Assert.assertTrue(calculate(StandardOperation.OR, TRUE, TRUE, TRUE));
    Assert.assertTrue(calculate(StandardOperation.OR, TRUE, TRUE, FALSE));
    Assert.assertTrue(calculate(StandardOperation.OR, TRUE, FALSE, TRUE));
    Assert.assertTrue(calculate(StandardOperation.OR, TRUE, FALSE, FALSE));
    Assert.assertTrue(calculate(StandardOperation.OR, FALSE, TRUE, TRUE));
    Assert.assertTrue(calculate(StandardOperation.OR, FALSE, TRUE, FALSE));
    Assert.assertTrue(calculate(StandardOperation.OR, FALSE, FALSE, TRUE));
    Assert.assertFalse(calculate(StandardOperation.OR, FALSE, FALSE, FALSE));
  }

  @Test
  public void testXorOperation() {
    Assert.assertFalse(calculate(StandardOperation.XOR, FALSE, FALSE));
    Assert.assertTrue(calculate(StandardOperation.XOR, TRUE, FALSE));
    Assert.assertTrue(calculate(StandardOperation.XOR, FALSE, TRUE));
    Assert.assertFalse(calculate(StandardOperation.XOR, TRUE, TRUE));

    Assert.assertTrue(calculate(StandardOperation.XOR, TRUE, TRUE, TRUE));
    Assert.assertFalse(calculate(StandardOperation.XOR, TRUE, TRUE, FALSE));
    Assert.assertFalse(calculate(StandardOperation.XOR, TRUE, FALSE, TRUE));
    Assert.assertTrue(calculate(StandardOperation.XOR, TRUE, FALSE, FALSE));
    Assert.assertFalse(calculate(StandardOperation.XOR, FALSE, TRUE, TRUE));
    Assert.assertTrue(calculate(StandardOperation.XOR, FALSE, TRUE, FALSE));
    Assert.assertTrue(calculate(StandardOperation.XOR, FALSE, FALSE, TRUE));
    Assert.assertFalse(calculate(StandardOperation.XOR, FALSE, FALSE, FALSE));
  }

  @Test
  public void testImplOperation() {
    Assert.assertTrue(calculate(StandardOperation.IMPL, FALSE, FALSE));
    Assert.assertFalse(calculate(StandardOperation.IMPL, TRUE, FALSE));
    Assert.assertTrue(calculate(StandardOperation.IMPL, FALSE, TRUE));
    Assert.assertTrue(calculate(StandardOperation.IMPL, TRUE, TRUE));
  }
}
