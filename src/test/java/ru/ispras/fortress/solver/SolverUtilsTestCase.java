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

import java.io.File;

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
    public static void init()
    {
        if (Environment.isUnix())
        {
            Environment.setSolverPath("tools/z3/bin/z3");
        }
        else if(Environment.isWindows())
        {
            Environment.setSolverPath("tools/z3/bin/z3.exe");
        }
        else if (Environment.isOSX())
        {
            Environment.setSolverPath("tools/z3/bin/z3");
        }
        else
        {
            fail("Unsupported platform. Please set up paths to the external" +
                 " engine. Platform name: " + System.getProperty("os.name"));
        }

        assertTrue("The solver engine executable is not found. Path: " +
            Environment.getSolverPath(),
            new File(Environment.getSolverPath()).isFile()
        );
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

        final NodeVariable x = new NodeVariable(new Variable("x", DataType.INTEGER));
        assertTrue(SolverUtils.isCondition(
            new NodeOperation(
                StandardOperation.OR,
                new NodeOperation(StandardOperation.GREATEREQ, x, NodeValue.newInteger(0)),
                new NodeOperation(StandardOperation.LESS, x, NodeValue.newInteger(10))
                )
            )
        );
    }

    @Test
    public void testIsAtomicCondition()
    {
        assertTrue(SolverUtils.isAtomicCondition(NodeValue.newBoolean(true)));
        assertTrue(SolverUtils.isAtomicCondition(NodeValue.newBoolean(false)));
        
        assertTrue(SolverUtils.isAtomicCondition(
            new NodeOperation(
                StandardOperation.EQ,
                NodeValue.newInteger(1),
                NodeValue.newInteger(2))
            )
        );

        assertFalse(SolverUtils.isAtomicCondition(
            new NodeOperation(
                StandardOperation.ADD,
                NodeValue.newInteger(1),
                NodeValue.newInteger(2))
            )
        );

        final NodeVariable x = new NodeVariable(new Variable("x", DataType.INTEGER));
        assertFalse(SolverUtils.isAtomicCondition(
            new NodeOperation(
                StandardOperation.OR,
                new NodeOperation(StandardOperation.GREATEREQ, x, NodeValue.newInteger(0)),
                new NodeOperation(StandardOperation.LESS, x, NodeValue.newInteger(10))
                )
            )
        );
    }
    
    @Test
    public void testGetConjunction()
    {
        // TODO
    }
    
    @Test
    public void testGetDisjunction()
    {
        // TODO
    }
    
    @Test
    public void testGetNegation()
    {
        // TODO      
    }
    
    @Test
    public void testGetComplement()
    {
        // TODO
    }

    @Test
    public void testAreComplete()
    {
        final NodeVariable x = new NodeVariable(new Variable("x", DataType.INTEGER));
        assertTrue(SolverUtils.areComplete(
            new NodeOperation(StandardOperation.GREATEREQ, x, NodeValue.newInteger(0)),
            new NodeOperation(StandardOperation.LESS, x, NodeValue.newInteger(10))
            )
        );

        assertTrue(SolverUtils.areComplete(
            new NodeOperation(StandardOperation.LESS, x, NodeValue.newInteger(0)),
            new NodeOperation(StandardOperation.GREATEREQ, x, NodeValue.newInteger(10))
            )
        );
    }

    @Test
    public void testAreCompatible()
    {
        final NodeVariable x = new NodeVariable(new Variable("x", DataType.INTEGER));
        assertTrue(SolverUtils.areCompatible(
            new NodeOperation(StandardOperation.GREATEREQ, x, NodeValue.newInteger(0)),
            new NodeOperation(StandardOperation.LESS, x, NodeValue.newInteger(10))
            )
        );

        assertFalse(SolverUtils.areCompatible(
            new NodeOperation(StandardOperation.LESS, x, NodeValue.newInteger(0)),
            new NodeOperation(StandardOperation.GREATEREQ, x, NodeValue.newInteger(10))
            )
        );
    }
}
