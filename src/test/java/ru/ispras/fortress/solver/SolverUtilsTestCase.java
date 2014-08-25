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
import org.junit.Test;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeBinding;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.StandardOperation;

public final class SolverUtilsTestCase
{
    private static final NodeVariable x =
        new NodeVariable(new Variable("x", DataType.INTEGER));

    private static final NodeVariable y =
        new NodeVariable(new Variable("y", DataType.INTEGER));

    private static final NodeVariable z =
        new NodeVariable(new Variable("z", DataType.INTEGER));

    private static final NodeVariable i =
        new NodeVariable(new Variable("i", DataType.INTEGER));

    private static final NodeVariable j =
        new NodeVariable(new Variable("j", DataType.INTEGER));
    
    private static final Node xEq0 =
        new NodeOperation(StandardOperation.EQ, x, NodeValue.newInteger(0));

    private static final Node yEq5 =
        new NodeOperation(StandardOperation.EQ, y, NodeValue.newInteger(5));

    private static final Node zEq10 =
        new NodeOperation(StandardOperation.EQ, z, NodeValue.newInteger(10));
    
    private static final Node iEq15 =
         new NodeOperation(StandardOperation.EQ, i, NodeValue.newInteger(15));

    private static final Node jEq20 =
         new NodeOperation(StandardOperation.EQ, j, NodeValue.newInteger(20));

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
        final Node iEq15ORjEq20 =
            new NodeOperation(StandardOperation.OR, iEq15, jEq20);

        final Node expected = new NodeOperation(
            StandardOperation.AND, xEq0, yEq5, zEq10, iEq15ORjEq20);

        final Node actual = SolverUtils.getConjunction(
            xEq0, yEq5, zEq10, iEq15ORjEq20);

        assertEquals(expected, actual);
    }
    
    @Test
    public void testGetDisjunction()
    {
        final Node iEq15ANDjEq20 =
            new NodeOperation(StandardOperation.AND, iEq15, jEq20);

        final Node expected = new NodeOperation(
            StandardOperation.OR, xEq0, yEq5, zEq10, iEq15ANDjEq20);

        final Node actual = SolverUtils.getDisjunction(
            xEq0, yEq5, zEq10, iEq15ANDjEq20);

        assertEquals(expected, actual);
    }

    @Test
    public void testGetNegation()
    {
        final Node iEq15ORjEq20 =
           new NodeOperation(StandardOperation.OR, iEq15, jEq20);

        final Node expected = new NodeOperation(StandardOperation.NOT, 
            new NodeOperation(StandardOperation.AND, xEq0, yEq5, zEq10, iEq15ORjEq20));

        final Node actual = SolverUtils.getNegation(
             xEq0, yEq5, zEq10, iEq15ORjEq20);

        assertEquals(expected, actual);   
    }

    @Test
    public void testGetComplement()
    {
        final Node iEq15ANDjEq20 =
            new NodeOperation(StandardOperation.AND, iEq15, jEq20);

        final Node expected = new NodeOperation(StandardOperation.NOT, 
            new NodeOperation(StandardOperation.OR, xEq0, yEq5, zEq10, iEq15ANDjEq20));

        final Node actual = SolverUtils.getComplement(
            xEq0, yEq5, zEq10, iEq15ANDjEq20);

        assertEquals(expected, actual);
    }

    @Test
    public void testAreComplete()
    {
        assertTrue(SolverUtils.areComplete(
            new NodeOperation(StandardOperation.GREATEREQ, x, NodeValue.newInteger(0)),
            new NodeOperation(StandardOperation.LESS, x, NodeValue.newInteger(10))
            )
        );

        assertFalse(SolverUtils.areComplete(
            new NodeOperation(StandardOperation.LESS, x, NodeValue.newInteger(0)),
            new NodeOperation(StandardOperation.GREATEREQ, x, NodeValue.newInteger(10))
            )
        );
    }

    @Test
    public void testAreCompatible()
    {
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

    @Test
    public void testHasBindings()
    {
        final Node noBindings = new NodeOperation(
            StandardOperation.AND,
            xEq0,
            yEq5,
            zEq10,
            new NodeOperation(StandardOperation.OR, iEq15, jEq20)
        );

        assertFalse(SolverUtils.hasBindings(noBindings));

        final NodeVariable a = new NodeVariable(new Variable("a", DataType.INTEGER));
        final NodeVariable b = new NodeVariable(new Variable("b", DataType.INTEGER));

        final Node bindings = new NodeOperation(
            StandardOperation.AND,
            xEq0,
            yEq5,
            zEq10,
            new NodeBinding(
                new NodeOperation(StandardOperation.OR, iEq15, jEq20),
                NodeBinding.bindVariable(a, NodeValue.newInteger(3)),
                NodeBinding.bindVariable(b, NodeValue.newInteger(4)),
                NodeBinding.bindVariable(i, new NodeOperation(StandardOperation.MUL, a, NodeValue.newInteger(5))),
                NodeBinding.bindVariable(j, new NodeOperation(StandardOperation.MUL, b, NodeValue.newInteger(5)))
            )
        );

        assertTrue(SolverUtils.hasBindings(bindings));
    }

    @Test
    public void testIsConstant()
    {
        final Node expr1 = new NodeOperation(
            StandardOperation.PLUS,
            NodeValue.newInteger(1),
            new NodeOperation(
                StandardOperation.MUL,
                NodeValue.newInteger(2),
                NodeValue.newInteger(3)
            ),
            new NodeOperation(
                StandardOperation.SUB,
                NodeValue.newInteger(20),
                new NodeOperation(
                    StandardOperation.MUL,
                    NodeValue.newInteger(2),
                    NodeValue.newInteger(5)
                )
            )
        );

        // Constant (no variables, no bindings). 
        assertTrue(SolverUtils.isConstant(expr1));

        final NodeVariable x = new NodeVariable(new Variable("x", DataType.INTEGER));
        final Node expr2 = new NodeOperation(
            StandardOperation.PLUS,
            NodeValue.newInteger(1),
            new NodeOperation(
                StandardOperation.MUL,
                NodeValue.newInteger(2),
                NodeValue.newInteger(3)
            ),
            new NodeOperation(
                StandardOperation.SUB,
                NodeValue.newInteger(20),
                new NodeOperation(
                    StandardOperation.MUL,
                    NodeValue.newInteger(2),
                    x
                )
            )
        );

        // Non-constant: has a variable 
        assertFalse(SolverUtils.isConstant(expr2));

        x.getVariable().setData(Data.newInteger(5));

        // Constant: has a variable, but it is assigned a value
        assertTrue(SolverUtils.isConstant(expr2));

        final NodeVariable y = new NodeVariable(new Variable("y", DataType.INTEGER));
        final Node expr3 = new NodeOperation(
            StandardOperation.PLUS,
            NodeValue.newInteger(1),
            new NodeOperation(
                StandardOperation.MUL,
                NodeValue.newInteger(2),
                NodeValue.newInteger(3)
            ),

            new NodeBinding(
                new NodeOperation(
                    StandardOperation.SUB,
                    NodeValue.newInteger(20),
                    new NodeOperation(StandardOperation.MUL, NodeValue.newInteger(2), y)
                ),
                NodeBinding.bindVariable(y, NodeValue.newInteger(10))
            )
        );

        // Constant: has a variable, but it is bound to a constant value
        assertTrue(SolverUtils.isConstant(expr3));

        final Node expr4 = new NodeOperation(
            StandardOperation.PLUS,
            NodeValue.newInteger(1),
            new NodeOperation(
                StandardOperation.MUL,
                NodeValue.newInteger(2),
                y
            ),

            new NodeBinding(
                new NodeOperation(
                    StandardOperation.SUB,
                    NodeValue.newInteger(20),
                    new NodeOperation(StandardOperation.MUL, NodeValue.newInteger(2), y)
                ),
                NodeBinding.bindVariable(y, NodeValue.newInteger(10))
            )
        );

        // Non-constant: has a variable, but it is bound to a constant value 
        //in all scopes it is used.
        assertFalse(SolverUtils.isConstant(expr4));
    }
}
