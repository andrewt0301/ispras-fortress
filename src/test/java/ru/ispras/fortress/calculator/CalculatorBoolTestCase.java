/*
 * Copyright (c) 2014 ISPRAS (www.ispras.ru)
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * CalculatorBoolTestCase.java, Sep 2, 2014 8:36:16 PM Alexander Kamkin
 * 
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not
 * use this file except in compliance with the License. You may obtain a copy of
 * the License at
 * 
 * http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations under
 * the License.
 */

package ru.ispras.fortress.calculator;

import static org.junit.Assert.*;
import org.junit.Test;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.expression.StandardOperation;

public final class CalculatorBoolTestCase
{
    private static final Data TRUE  = Data.newBoolean(true);
    private static final Data FALSE = Data.newBoolean(false);

    public static boolean calculate(final Enum<?> operationId, final Data ... operands)
    {
        final Data data = Calculator.calculate(operationId, operands);
        return ((Boolean) data.getValue()).booleanValue();
    }

    @Test
    public void testNotOperation()
    {
        assertFalse (calculate(StandardOperation.NOT, TRUE));
        assertTrue  (calculate(StandardOperation.NOT, FALSE));
    }

    @Test
    public void testAndOperation()
    {
        assertFalse (calculate(StandardOperation.AND, FALSE, FALSE));
        assertFalse (calculate(StandardOperation.AND, TRUE,  FALSE));
        assertFalse (calculate(StandardOperation.AND, FALSE, TRUE));
        assertTrue  (calculate(StandardOperation.AND, TRUE,  TRUE));

        assertTrue  (calculate(StandardOperation.AND, TRUE,  TRUE,  TRUE));
        assertFalse (calculate(StandardOperation.AND, TRUE,  TRUE,  FALSE));
        assertFalse (calculate(StandardOperation.AND, TRUE,  FALSE, TRUE));
        assertFalse (calculate(StandardOperation.AND, TRUE,  FALSE, FALSE));
        assertFalse (calculate(StandardOperation.AND, FALSE, TRUE,  TRUE));
        assertFalse (calculate(StandardOperation.AND, FALSE, TRUE,  FALSE));
        assertFalse (calculate(StandardOperation.AND, FALSE, FALSE, TRUE));
        assertFalse (calculate(StandardOperation.AND, FALSE, FALSE, FALSE));
    }

    @Test
    public void testOrOperation()
    {
        assertFalse (calculate(StandardOperation.OR, FALSE, FALSE));
        assertTrue  (calculate(StandardOperation.OR, TRUE,  FALSE));
        assertTrue  (calculate(StandardOperation.OR, FALSE, TRUE));
        assertTrue  (calculate(StandardOperation.OR, TRUE,  TRUE));

        assertTrue  (calculate(StandardOperation.OR, TRUE,  TRUE,  TRUE));
        assertTrue  (calculate(StandardOperation.OR, TRUE,  TRUE,  FALSE));
        assertTrue  (calculate(StandardOperation.OR, TRUE,  FALSE, TRUE));
        assertTrue  (calculate(StandardOperation.OR, TRUE,  FALSE, FALSE));
        assertTrue  (calculate(StandardOperation.OR, FALSE, TRUE,  TRUE));
        assertTrue  (calculate(StandardOperation.OR, FALSE, TRUE,  FALSE));
        assertTrue  (calculate(StandardOperation.OR, FALSE, FALSE, TRUE));
        assertFalse (calculate(StandardOperation.OR, FALSE, FALSE, FALSE));
    }

    @Test
    public void testXorOperation()
    {
        assertFalse (calculate(StandardOperation.XOR, FALSE, FALSE));
        assertTrue  (calculate(StandardOperation.XOR, TRUE,  FALSE));
        assertTrue  (calculate(StandardOperation.XOR, FALSE, TRUE));
        assertFalse (calculate(StandardOperation.XOR, TRUE,  TRUE));

        assertTrue  (calculate(StandardOperation.XOR, TRUE,  TRUE,  TRUE));
        assertFalse (calculate(StandardOperation.XOR, TRUE,  TRUE,  FALSE));
        assertFalse (calculate(StandardOperation.XOR, TRUE,  FALSE, TRUE));
        assertTrue  (calculate(StandardOperation.XOR, TRUE,  FALSE, FALSE));
        assertFalse (calculate(StandardOperation.XOR, FALSE, TRUE,  TRUE));
        assertTrue  (calculate(StandardOperation.XOR, FALSE, TRUE,  FALSE));
        assertTrue  (calculate(StandardOperation.XOR, FALSE, FALSE, TRUE));
        assertFalse (calculate(StandardOperation.XOR, FALSE, FALSE, FALSE));
    }

    @Test
    public void testImplOperation()
    {
        assertTrue  (calculate(StandardOperation.IMPL, FALSE, FALSE));
        assertFalse (calculate(StandardOperation.IMPL, TRUE,  FALSE));
        assertTrue  (calculate(StandardOperation.IMPL, FALSE, TRUE));
        assertTrue  (calculate(StandardOperation.IMPL, TRUE,  TRUE));
    }
}
