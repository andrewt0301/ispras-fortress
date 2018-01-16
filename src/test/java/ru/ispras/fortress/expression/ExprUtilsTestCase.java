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

package ru.ispras.fortress.expression;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.data.types.bitvector.BitVector;

import org.junit.Assert;
import org.junit.Test;

public final class ExprUtilsTestCase {
  private static final NodeVariable X = new NodeVariable(new Variable("x", DataType.INTEGER));
  private static final NodeVariable Y = new NodeVariable(new Variable("y", DataType.INTEGER));
  private static final NodeVariable Z = new NodeVariable(new Variable("z", DataType.INTEGER));
  private static final NodeVariable I = new NodeVariable(new Variable("i", DataType.INTEGER));
  private static final NodeVariable J = new NodeVariable(new Variable("j", DataType.INTEGER));

  private static final Node XEq0 = Nodes.eq(X, NodeValue.newInteger(0));
  private static final Node YEq5 = Nodes.eq(Y, NodeValue.newInteger(5));
  private static final Node ZEq10 = Nodes.eq(Z, NodeValue.newInteger(10));
  private static final Node IEq15 = Nodes.eq(I, NodeValue.newInteger(15));
  private static final Node JEq20 = Nodes.eq(J, NodeValue.newInteger(20));

  @Test
  public void testIsCondition() {
    Assert.assertTrue(ExprUtils.isCondition(NodeValue.newBoolean(true)));
    Assert.assertTrue(ExprUtils.isCondition(NodeValue.newBoolean(false)));
    Assert.assertFalse(ExprUtils.isCondition(NodeValue.newInteger(0)));
    Assert.assertFalse(ExprUtils.isCondition(NodeValue.newReal(0)));

    Assert.assertTrue(ExprUtils.isCondition(new NodeVariable(new Variable("x", DataType.BOOLEAN))));
    Assert.assertFalse(
        ExprUtils.isCondition(new NodeVariable(new Variable("y", DataType.INTEGER))));
    Assert.assertTrue(
        ExprUtils.isCondition(Nodes.eq(NodeValue.newInteger(1), NodeValue.newInteger(2))));
    Assert.assertFalse(
        ExprUtils.isCondition(Nodes.add(NodeValue.newInteger(1), NodeValue.newInteger(2))));

    Assert.assertTrue(ExprUtils.isCondition(Nodes.or(
        Nodes.GREATEREQ(X, NodeValue.newInteger(0)),
        Nodes.LESS(X, NodeValue.newInteger(10)))));
  }

  @Test
  public void testIsAtomicCondition() {
    Assert.assertTrue(ExprUtils.isAtomicCondition(NodeValue.newBoolean(true)));
    Assert.assertTrue(ExprUtils.isAtomicCondition(NodeValue.newBoolean(false)));

    Assert.assertTrue(ExprUtils.isAtomicCondition(
        Nodes.eq(NodeValue.newInteger(1), NodeValue.newInteger(2))));

    Assert.assertFalse(ExprUtils.isAtomicCondition(
        Nodes.add(NodeValue.newInteger(1), NodeValue.newInteger(2))));

    Assert.assertFalse(ExprUtils.isAtomicCondition(Nodes.or(
        Nodes.GREATEREQ(X, NodeValue.newInteger(0)),
        Nodes.LESS(X, NodeValue.newInteger(10)))));
  }

  @Test
  public void testGetConjunction() {
    final Node iEq15ORjEq20 = Nodes.or(IEq15, JEq20);

    final Node expected = Nodes.and(XEq0, YEq5, ZEq10, iEq15ORjEq20);
    final Node actual = ExprUtils.getConjunction(XEq0, YEq5, ZEq10, iEq15ORjEq20);

    Assert.assertEquals(expected, actual);
  }

  @Test
  public void testGetDisjunction() {
    final Node iEq15AndjEq20 = Nodes.and(IEq15, JEq20);

    final Node expected = Nodes.or(XEq0, YEq5, ZEq10, iEq15AndjEq20);
    final Node actual = ExprUtils.getDisjunction(XEq0, YEq5, ZEq10, iEq15AndjEq20);

    Assert.assertEquals(expected, actual);
  }

  @Test
  public void testGetNegation() {
    final Node iEq15ORjEq20 = Nodes.or(IEq15, JEq20);

    final Node expected = Nodes.not(Nodes.and(XEq0, YEq5, ZEq10, iEq15ORjEq20));
    final Node actual = ExprUtils.getNegation(XEq0, YEq5, ZEq10, iEq15ORjEq20);

    Assert.assertEquals(expected, actual);
  }

  @Test
  public void testGetComplement() {
    final Node iEq15AndjEq20 = Nodes.and(IEq15, JEq20);

    final Node expected = Nodes.not(Nodes.or(XEq0, YEq5, ZEq10, iEq15AndjEq20));
    final Node actual = ExprUtils.getComplement(XEq0, YEq5, ZEq10, iEq15AndjEq20);

    Assert.assertEquals(expected, actual);
  }

  @Test
  public void testAreComplete() {
    Assert.assertTrue(ExprUtils.areComplete(
        Nodes.GREATEREQ(X, NodeValue.newInteger(0)),
        Nodes.LESS(X, NodeValue.newInteger(10))));

    Assert.assertFalse(ExprUtils.areComplete(
        Nodes.LESS(X, NodeValue.newInteger(0)),
        Nodes.GREATEREQ(X, NodeValue.newInteger(10))));
  }

  @Test
  public void testAreCompatible() {
    Assert.assertTrue(ExprUtils.areCompatible(
        Nodes.GREATEREQ(X, NodeValue.newInteger(0)),
        Nodes.LESS(X, NodeValue.newInteger(10))));

    Assert.assertFalse(ExprUtils.areCompatible(
        Nodes.LESS(X, NodeValue.newInteger(0)),
        Nodes.GREATEREQ(X, NodeValue.newInteger(10))));
  }

  @Test
  public void testHasBindings() {
    final Node noBindings = Nodes.and(XEq0, YEq5, ZEq10, Nodes.or(IEq15, JEq20));
    Assert.assertFalse(ExprUtils.hasBindings(noBindings));

    final NodeVariable a = new NodeVariable(new Variable("a", DataType.INTEGER));
    final NodeVariable b = new NodeVariable(new Variable("b", DataType.INTEGER));

    final Node bindings = Nodes.and(
        XEq0,
        YEq5,
        ZEq10,
        new NodeBinding(
            Nodes.or(IEq15, JEq20),
            NodeBinding.bindVariable(a, NodeValue.newInteger(3)),
            NodeBinding.bindVariable(b, NodeValue.newInteger(4)),
            NodeBinding.bindVariable(I, Nodes.mul(a, NodeValue.newInteger(5))),
            NodeBinding.bindVariable(J, Nodes.mul(b, NodeValue.newInteger(5)))
            )
        );

    Assert.assertTrue(ExprUtils.hasBindings(bindings));
  }

  @Test
  public void testIsConstant() {
    final Node expr1 = Nodes.add(
        NodeValue.newInteger(1),
        Nodes.mul(NodeValue.newInteger(2), NodeValue.newInteger(3)),
        Nodes.sub(NodeValue.newInteger(20),
                  Nodes.mul(NodeValue.newInteger(2), NodeValue.newInteger(5))));

    // Constant (no variables, no bindings).
    Assert.assertTrue(ExprUtils.isConstant(expr1));

    final NodeVariable x = new NodeVariable(new Variable("x", DataType.INTEGER));
    final Node expr2 = Nodes.add(
        NodeValue.newInteger(1),
        Nodes.mul(NodeValue.newInteger(2), NodeValue.newInteger(3)),
        Nodes.sub(NodeValue.newInteger(20), Nodes.mul(NodeValue.newInteger(2), x)));

    // Non-constant: has a variable
    Assert.assertFalse(ExprUtils.isConstant(expr2));

    x.getVariable().setData(Data.newInteger(5));

    // Constant: has a variable, but it is assigned a value
    Assert.assertTrue(ExprUtils.isConstant(expr2));

    final NodeVariable y = new NodeVariable(new Variable("y", DataType.INTEGER));
    final Node expr3 = Nodes.add(
        NodeValue.newInteger(1),
        Nodes.mul(NodeValue.newInteger(2), NodeValue.newInteger(3)),
        new NodeBinding(
            Nodes.sub(NodeValue.newInteger(20), Nodes.mul(NodeValue.newInteger(2), y)),
            NodeBinding.bindVariable(y, NodeValue.newInteger(10))));

    // Constant: has a variable, but it is bound to a constant value
    Assert.assertTrue(ExprUtils.isConstant(expr3));

    final Node expr4 = Nodes.add(
        NodeValue.newInteger(1),
        Nodes.mul(NodeValue.newInteger(2), y),
        new NodeBinding(Nodes.sub(NodeValue.newInteger(20),
            Nodes.mul(NodeValue.newInteger(2), y)),
            NodeBinding.bindVariable(y, NodeValue.newInteger(10))));

    // Non-constant: has a variable, but it is bound to a constant value
    // in all scopes it is used.
    Assert.assertFalse(ExprUtils.isConstant(expr4));
  }

  @Test
  public void testIsSat() {
    Assert.assertTrue(ExprUtils.isSAT(NodeValue.newBoolean(true)));
    Assert.assertFalse(ExprUtils.isSAT(NodeValue.newBoolean(false)));

    Assert.assertTrue(ExprUtils.isSAT(
        Nodes.eq(
            NodeValue.newInteger(5),
            Nodes.add(NodeValue.newInteger(2), NodeValue.newInteger(3)))));

    Assert.assertFalse(ExprUtils.isSAT(
        Nodes.eq(
            NodeValue.newInteger(5),
            Nodes.add(NodeValue.newInteger(2), NodeValue.newInteger(-3)))));
  }

  @Test
  public void testIsKind() {
    Assert.assertTrue(ExprUtils.isKind(
        Node.Kind.VALUE,
        NodeValue.newInteger(10),
        NodeValue.newReal(3.14),
        NodeValue.newBitVector(BitVector.valueOf(0xDEADBEEF, 32))));

    Assert.assertFalse(ExprUtils.isKind(
        Node.Kind.VALUE,
        NodeValue.newInteger(10),
        NodeValue.newReal(3.14),
        Nodes.add(NodeValue.newInteger(10), NodeValue.newInteger(20)),
        NodeValue.newBitVector(BitVector.valueOf(0xDEADBEEF, 32))));

    Assert.assertTrue(ExprUtils.isKind(
        Node.Kind.OPERATION,
        Nodes.add(NodeValue.newInteger(10), NodeValue.newInteger(20)),
        Nodes.sub(NodeValue.newInteger(10), NodeValue.newInteger(20)),
        Nodes.MOD(NodeValue.newInteger(10), NodeValue.newInteger(20))));
  }
}
