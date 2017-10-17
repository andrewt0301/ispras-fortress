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

package ru.ispras.fortress.expression;

import static org.junit.Assert.*;
import org.junit.Test;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.data.types.bitvector.BitVector;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeBinding;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;

public final class ExprUtilsTestCase {
  private static final NodeVariable X = new NodeVariable(new Variable("x", DataType.INTEGER));
  private static final NodeVariable Y = new NodeVariable(new Variable("y", DataType.INTEGER));
  private static final NodeVariable Z = new NodeVariable(new Variable("z", DataType.INTEGER));
  private static final NodeVariable I = new NodeVariable(new Variable("i", DataType.INTEGER));
  private static final NodeVariable J = new NodeVariable(new Variable("j", DataType.INTEGER));

  private static final Node XEq0 = Nodes.EQ(X, NodeValue.newInteger(0));
  private static final Node YEq5 = Nodes.EQ(Y, NodeValue.newInteger(5));
  private static final Node ZEq10 = Nodes.EQ(Z, NodeValue.newInteger(10));
  private static final Node IEq15 = Nodes.EQ(I, NodeValue.newInteger(15));
  private static final Node JEq20 = Nodes.EQ(J, NodeValue.newInteger(20));

  @Test
  public void testIsCondition() {
    assertTrue(ExprUtils.isCondition(NodeValue.newBoolean(true)));
    assertTrue(ExprUtils.isCondition(NodeValue.newBoolean(false)));
    assertFalse(ExprUtils.isCondition(NodeValue.newInteger(0)));
    assertFalse(ExprUtils.isCondition(NodeValue.newReal(0)));

    assertTrue(ExprUtils.isCondition(new NodeVariable(new Variable("x", DataType.BOOLEAN))));
    assertFalse(ExprUtils.isCondition(new NodeVariable(new Variable("y", DataType.INTEGER))));
    assertTrue(ExprUtils.isCondition(Nodes.EQ(NodeValue.newInteger(1), NodeValue.newInteger(2))));
    assertFalse(ExprUtils.isCondition(Nodes.ADD(NodeValue.newInteger(1), NodeValue.newInteger(2))));

    assertTrue(ExprUtils.isCondition(Nodes.OR(
        Nodes.GREATEREQ(X, NodeValue.newInteger(0)),
        Nodes.LESS(X, NodeValue.newInteger(10)))));
  }

  @Test
  public void testIsAtomicCondition() {
    assertTrue(ExprUtils.isAtomicCondition(NodeValue.newBoolean(true)));
    assertTrue(ExprUtils.isAtomicCondition(NodeValue.newBoolean(false)));

    assertTrue(ExprUtils.isAtomicCondition(
        Nodes.EQ(NodeValue.newInteger(1), NodeValue.newInteger(2))));

    assertFalse(ExprUtils.isAtomicCondition(
        Nodes.ADD(NodeValue.newInteger(1), NodeValue.newInteger(2))));

    assertFalse(ExprUtils.isAtomicCondition(Nodes.OR(
        Nodes.GREATEREQ(X, NodeValue.newInteger(0)),
        Nodes.LESS(X, NodeValue.newInteger(10)))));
  }

  @Test
  public void testGetConjunction() {
    final Node iEq15ORjEq20 = Nodes.OR(IEq15, JEq20);

    final Node expected = Nodes.AND(XEq0, YEq5, ZEq10, iEq15ORjEq20);
    final Node actual = ExprUtils.getConjunction(XEq0, YEq5, ZEq10, iEq15ORjEq20);

    assertEquals(expected, actual);
  }

  @Test
  public void testGetDisjunction() {
    final Node iEq15ANDjEq20 = Nodes.AND(IEq15, JEq20);

    final Node expected = Nodes.OR(XEq0, YEq5, ZEq10, iEq15ANDjEq20);
    final Node actual = ExprUtils.getDisjunction(XEq0, YEq5, ZEq10, iEq15ANDjEq20);

    assertEquals(expected, actual);
  }

  @Test
  public void testGetNegation() {
    final Node iEq15ORjEq20 = Nodes.OR(IEq15, JEq20);

    final Node expected = Nodes.NOT(Nodes.AND(XEq0, YEq5, ZEq10, iEq15ORjEq20));
    final Node actual = ExprUtils.getNegation(XEq0, YEq5, ZEq10, iEq15ORjEq20);

    assertEquals(expected, actual);
  }

  @Test
  public void testGetComplement() {
    final Node iEq15ANDjEq20 = Nodes.AND(IEq15, JEq20);

    final Node expected = Nodes.NOT(Nodes.OR(XEq0, YEq5, ZEq10, iEq15ANDjEq20));
    final Node actual = ExprUtils.getComplement(XEq0, YEq5, ZEq10, iEq15ANDjEq20);

    assertEquals(expected, actual);
  }

  @Test
  public void testAreComplete() {
    assertTrue(ExprUtils.areComplete(
        Nodes.GREATEREQ(X, NodeValue.newInteger(0)),
        Nodes.LESS(X, NodeValue.newInteger(10))));

    assertFalse(ExprUtils.areComplete(
        Nodes.LESS(X, NodeValue.newInteger(0)),
        Nodes.GREATEREQ(X, NodeValue.newInteger(10))));
  }

  @Test
  public void testAreCompatible() {
    assertTrue(ExprUtils.areCompatible(
        Nodes.GREATEREQ(X, NodeValue.newInteger(0)),
        Nodes.LESS(X, NodeValue.newInteger(10))));

    assertFalse(ExprUtils.areCompatible(
        Nodes.LESS(X, NodeValue.newInteger(0)),
        Nodes.GREATEREQ(X, NodeValue.newInteger(10))));
  }

  @Test
  public void testHasBindings() {
    final Node noBindings = Nodes.AND(XEq0, YEq5, ZEq10, Nodes.OR(IEq15, JEq20));
    assertFalse(ExprUtils.hasBindings(noBindings));

    final NodeVariable a = new NodeVariable(new Variable("a", DataType.INTEGER));
    final NodeVariable b = new NodeVariable(new Variable("b", DataType.INTEGER));

    final Node bindings = Nodes.AND(
        XEq0,
        YEq5,
        ZEq10,
        new NodeBinding(
            Nodes.OR(IEq15, JEq20),
            NodeBinding.bindVariable(a, NodeValue.newInteger(3)),
            NodeBinding.bindVariable(b, NodeValue.newInteger(4)),
            NodeBinding.bindVariable(I, Nodes.MUL(a, NodeValue.newInteger(5))),
            NodeBinding.bindVariable(J, Nodes.MUL(b, NodeValue.newInteger(5)))
            )
        );

    assertTrue(ExprUtils.hasBindings(bindings));
  }

  @Test
  public void testIsConstant() {
    final Node expr1 = Nodes.ADD(
        NodeValue.newInteger(1),
        Nodes.MUL(NodeValue.newInteger(2), NodeValue.newInteger(3)),
        Nodes.SUB(NodeValue.newInteger(20),
                  Nodes.MUL(NodeValue.newInteger(2), NodeValue.newInteger(5))));

    // Constant (no variables, no bindings).
    assertTrue(ExprUtils.isConstant(expr1));

    final NodeVariable x = new NodeVariable(new Variable("x", DataType.INTEGER));
    final Node expr2 = Nodes.ADD(
        NodeValue.newInteger(1),
        Nodes.MUL(NodeValue.newInteger(2), NodeValue.newInteger(3)),
        Nodes.SUB(NodeValue.newInteger(20), Nodes.MUL(NodeValue.newInteger(2), x)));

    // Non-constant: has a variable
    assertFalse(ExprUtils.isConstant(expr2));

    x.getVariable().setData(Data.newInteger(5));

    // Constant: has a variable, but it is assigned a value
    assertTrue(ExprUtils.isConstant(expr2));

    final NodeVariable y = new NodeVariable(new Variable("y", DataType.INTEGER));
    final Node expr3 = Nodes.ADD(
        NodeValue.newInteger(1),
        Nodes.MUL(NodeValue.newInteger(2), NodeValue.newInteger(3)),
        new NodeBinding(
            Nodes.SUB(NodeValue.newInteger(20), Nodes.MUL(NodeValue.newInteger(2), y)),
            NodeBinding.bindVariable(y, NodeValue.newInteger(10))));

    // Constant: has a variable, but it is bound to a constant value
    assertTrue(ExprUtils.isConstant(expr3));

    final Node expr4 = Nodes.ADD(
        NodeValue.newInteger(1),
        Nodes.MUL(NodeValue.newInteger(2), y),
        new NodeBinding(Nodes.SUB(NodeValue.newInteger(20), 
            Nodes.MUL(NodeValue.newInteger(2), y)),
            NodeBinding.bindVariable(y, NodeValue.newInteger(10))));

    // Non-constant: has a variable, but it is bound to a constant value
    // in all scopes it is used.
    assertFalse(ExprUtils.isConstant(expr4));
  }

  @Test
  public void testIsSat() {
    assertTrue(ExprUtils.isSAT(NodeValue.newBoolean(true)));
    assertFalse(ExprUtils.isSAT(NodeValue.newBoolean(false)));

    assertTrue(ExprUtils.isSAT(
        Nodes.EQ(
            NodeValue.newInteger(5),
            Nodes.ADD(NodeValue.newInteger(2), NodeValue.newInteger(3)))));

    assertFalse(ExprUtils.isSAT(
        Nodes.EQ(
            NodeValue.newInteger(5),
            Nodes.ADD(NodeValue.newInteger(2), NodeValue.newInteger(-3)))));
  }

  @Test
  public void testIsKind() {
    assertTrue(ExprUtils.isKind(
        Node.Kind.VALUE,
        NodeValue.newInteger(10),
        NodeValue.newReal(3.14),
        NodeValue.newBitVector(BitVector.valueOf(0xDEADBEEF, 32))));

    assertFalse(ExprUtils.isKind(
        Node.Kind.VALUE,
        NodeValue.newInteger(10),
        NodeValue.newReal(3.14),
        Nodes.ADD(NodeValue.newInteger(10), NodeValue.newInteger(20)),
        NodeValue.newBitVector(BitVector.valueOf(0xDEADBEEF, 32))));

    assertTrue(ExprUtils.isKind(
        Node.Kind.OPERATION,
        Nodes.ADD(NodeValue.newInteger(10), NodeValue.newInteger(20)),
        Nodes.SUB(NodeValue.newInteger(10), NodeValue.newInteger(20)),
        Nodes.MOD(NodeValue.newInteger(10), NodeValue.newInteger(20))));
  }
}
