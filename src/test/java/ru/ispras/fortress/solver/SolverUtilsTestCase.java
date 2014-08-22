/*
 * Copyright (c) 2014 ISPRAS (www.ispras.ru)
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * SolverUtilsTestCase.java, Aug 22, 2014 5:15:41 PM Andrei Tatarnikov
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

package ru.ispras.fortress.solver;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.StandardOperation;

public class SolverUtilsTestCase
{
    @BeforeClass
    public static void setUpBeforeClass() throws Exception
    {
    }
    
    @Before
    public void setUp() throws Exception
    {
    }

    @Test
    public void testIsCondition()
    {
        assertTrue(SolverUtils.isCondition(NodeValue.newBoolean(true)));
        assertTrue(SolverUtils.isCondition(NodeValue.newBoolean(false)));
        assertFalse(SolverUtils.isCondition(NodeValue.newInteger(0)));
        assertFalse(SolverUtils.isCondition(NodeValue.newReal(0)));

        assertTrue(SolverUtils.isCondition(
            new NodeVariable(new Variable("x", DataType.BOOLEAN))));
        assertFalse(SolverUtils.isCondition(
            new NodeVariable(new Variable("y", DataType.INTEGER))));

        assertTrue(SolverUtils.isCondition(
            new NodeOperation(
                StandardOperation.EQ,
                NodeValue.newInteger(1),
                NodeValue.newInteger(2))
            )
        );

        assertFalse(SolverUtils.isCondition(
            new NodeOperation(
                StandardOperation.ADD,
                NodeValue.newInteger(1),
                NodeValue.newInteger(2))
            )
        );
    }
}
