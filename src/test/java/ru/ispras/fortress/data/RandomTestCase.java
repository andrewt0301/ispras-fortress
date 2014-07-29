/*
 * Copyright (c) 2014 ISPRAS (www.ispras.ru)
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * RandomTestCase.java, Jul 28, 2014 9:26:24 PM Andrei Tatarnikov
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

package ru.ispras.fortress.data;

import static org.junit.Assert.*;

import org.junit.Test;

public class RandomTestCase
{
    @Test
    public void test()
    {
        Random.setSeed(100);

        generateAndCheck(DataType.BOOLEAN, Data.newBoolean(false));
        generateAndCheck(DataType.BOOLEAN, Data.newBoolean(true));
        generateAndCheck(DataType.BOOLEAN, Data.newBoolean(false));

        generateAndCheck(DataType.INTEGER, Data.newInteger(-444958197));
        generateAndCheck(DataType.INTEGER, Data.newInteger(73219576));
        generateAndCheck(DataType.INTEGER, Data.newInteger(799334993));

        generateAndCheck(DataType.BIT_VECTOR(16),
            Data.newBitVector("1000101000101111", 2, 16));
        generateAndCheck(DataType.BIT_VECTOR(16),
            Data.newBitVector("0100011111011111", 2, 16));
        generateAndCheck(DataType.BIT_VECTOR(16),
            Data.newBitVector("1011101111000000", 2, 16));

        tryToGenerateUnsupported(DataType.UNKNOWN);
        tryToGenerateUnsupported(DataType.REAL);

        System.out.println(Random.newVariable("x", DataType.INTEGER));
        System.out.println(Random.newVariable("y", DataType.INTEGER));

        final Variable a = new Variable("a", DataType.INTEGER);
        System.out.println(Random.assignValue(a));

        final Variable b = new Variable("b", DataType.INTEGER);
        System.out.println(Random.assignValue(b));
    }

    private static void generateAndCheck(DataType type, Data expected)
    {
        final Data current = Random.newValue(type);
        System.out.println(current);

        assertTrue(
            String.format("Current: %s, Extected: %s",
                current.getValue(),
                expected.getValue()
            ),
            current.equals(expected)
        );
    }

    private static void tryToGenerateUnsupported(DataType type)
    {
        boolean failed = false;

        try
        {
            Random.newValue(type);
        }
        catch (UnsupportedOperationException e)
        {
            failed = true;
            System.out.println(e.getMessage());
        }

        assertTrue(
            String.format("An attempt to generate random data for the %s type " + 
                          "is supposed to fail.", type.getTypeId()),
            failed
        );
    }
}
