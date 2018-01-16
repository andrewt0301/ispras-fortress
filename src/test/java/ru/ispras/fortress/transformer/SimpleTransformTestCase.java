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

package ru.ispras.fortress.transformer;

import org.junit.Assert;
import org.junit.Test;

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.types.bitvector.BitVector;
import ru.ispras.fortress.expression.ExprUtils;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeBinding;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.Nodes;
import ru.ispras.fortress.expression.StandardOperation;

import java.util.Collections;
import java.util.List;

public class SimpleTransformTestCase {
  private static NodeVariable newVariable(final String name) {
    return new NodeVariable(name, DataType.INTEGER);
  }

  private static NodeOperation PLUS(Node... args) {
    return new NodeOperation(StandardOperation.PLUS, args);
  }

  private static NodeOperation AND(Node... args) {
    return new NodeOperation(StandardOperation.AND, args);
  }

  private static NodeOperation EQ(Node... args) {
    return new NodeOperation(StandardOperation.EQ, args);
  }

  private static NodeOperation NOTEQ(Node... args) {
    return new NodeOperation(StandardOperation.NOTEQ, args);
  }

  private static NodeOperation GREATEREQ(Node... args) {
    return new NodeOperation(StandardOperation.GREATEREQ, args);
  }

  private static NodeOperation LESSEQ(Node... args) {
    return new NodeOperation(StandardOperation.LESSEQ, args);
  }

  private static NodeOperation OR(Node... args) {
    return new NodeOperation(StandardOperation.OR, args);
  }

  private static NodeOperation IMPL(Node... args) {
    return new NodeOperation(StandardOperation.IMPL, args);
  }

  private static NodeBinding singleBinding(NodeVariable variable, Node value, Node expr) {
    final List<NodeBinding.BoundVariable> bindings =
        Collections.singletonList(NodeBinding.bindVariable(variable, value));

    return new NodeBinding(expr, bindings);
  }

  @Test
  public void substituteSingleVariable() {
    final Node a = newVariable("a");
    final Node b = newVariable("b");
    final Node c = newVariable("c");

    // (a = b + c)
    final Node expr = EQ(a, PLUS(b, c));
    final Node firstExpected = EQ(a, PLUS(a, c));
    final Node firstPass = Transformer.substitute(expr, "b", a);
    Assert.assertTrue(firstExpected.toString().equals(firstPass.toString()));

    final Node secondExpected = EQ(c, PLUS(c, c));
    final Node secondPass = Transformer.substitute(firstPass, "a", c);
    Assert.assertTrue(secondExpected.toString().equals(secondPass.toString()));
  }

  @Test
  public void substituteWithinBinding() {
    final NodeVariable a = newVariable("a");
    final NodeVariable x = newVariable("x");
    final NodeVariable y = newVariable("y");

    final Node let = singleBinding(a, PLUS(x, y), PLUS(x, a));
    final Node unchanged = Transformer.substitute(let, "a", x);

    Assert.assertTrue(unchanged.toString().equals(let.toString()));

    final Node changed = Transformer.substitute(let, "x", y);
    final Node expected = singleBinding(a, PLUS(y, y), PLUS(y, a));

    Assert.assertTrue(changed.toString().equals(expected.toString()));
  }

  @Test
  public void substituteBinding() {
    final NodeVariable a = newVariable("a");
    final NodeVariable x = newVariable("x");
    final NodeVariable y = newVariable("y");

    final NodeBinding let = singleBinding(a, PLUS(x, y), PLUS(x, a));
    final Node unrolled = Transformer.substituteBinding(let);
    final Node expected = PLUS(x, PLUS(x, y));

    Assert.assertTrue(unrolled.toString().equals(expected.toString()));
  }

  @Test
  public void substituteAllBindings() {
    final NodeVariable a = newVariable("a");
    final NodeVariable x = newVariable("x");
    final NodeVariable y = newVariable("y");

    final NodeBinding letA = singleBinding(a, PLUS(x, y), PLUS(x, a));
    final NodeBinding letY = singleBinding(y, PLUS(x, x), letA);

    final Node unrolled = Transformer.substituteAllBindings(PLUS(y, letY));
    final Node expected = PLUS(y, PLUS(x, PLUS(x, PLUS(x, x))));

    Assert.assertTrue(unrolled.toString().equals(expected.toString()));
  }

  @Test
  public void standardizeBooleanEquality() {
    final NodeVariable x = newVariable("x");
    final NodeVariable y = newVariable("y");

    final Node equality = EQ(x, y);

    final Node booleanEquality = EQ(equality, Nodes.TRUE);
    final Node booleanInequality = EQ(Nodes.FALSE, EQ(x, y));

    final Node standardEquality = Transformer.standardize(booleanEquality);
    final Node standardInequality = Transformer.standardize(booleanInequality);

    Assert.assertTrue(standardEquality.toString().equals(equality.toString()));
    Assert.assertTrue(standardInequality.toString().equals(Nodes.not(equality).toString()));
  }

  @Test
  public void standardizeChainedBooleanEquality() {
    final NodeVariable x = newVariable("x");
    final NodeVariable y = newVariable("y");
    final NodeVariable z = newVariable("z");

    final Node eqxy = EQ(x, y);
    final Node eqxz = EQ(x, z);

    final Node equalsTrue = EQ(eqxy, Nodes.TRUE, eqxz);
    final Node equalsFalse = EQ(Nodes.FALSE, eqxy, eqxz);

    final Node expectedEquality = EQ(z, y, x);
    final Node standardEquality = Transformer.standardize(equalsTrue);

    final Node expectedInequality = AND(Nodes.not(eqxy), Nodes.not(eqxz));
    final Node standardInequality = Transformer.standardize(equalsFalse);

    Assert.assertTrue(standardEquality.toString().equals(expectedEquality.toString()));
    Assert.assertTrue(standardInequality.toString().equals(expectedInequality.toString()));
  }

  @Test
  public void standardizeImplication() {
    final NodeVariable x = newVariable("x");
    final NodeVariable y = newVariable("y");
    final NodeVariable z = newVariable("z");

    final Node eqxy = EQ(x, y);
    final Node eqxz = EQ(x, z);
    final Node eqyz = EQ(y, z);

    final Node impl2 = IMPL(eqxy, eqxz);
    final Node impl3 = IMPL(eqxy, eqxz, eqyz);

    final Node std2 = Transformer.standardize(impl2);
    final Node std3 = Transformer.standardize(impl3);

    Assert.assertTrue(std2.toString().equals(OR(Nodes.not(eqxy), eqxz).toString()));
    Assert.assertTrue(std3.toString().equals(
        OR(Nodes.not(eqxy), Nodes.not(eqxz), eqyz).toString()));
  }

  @Test
  public void standardizeConjunction() {
    final NodeVariable x = newVariable("x");
    final NodeVariable y = newVariable("y");
    final Node eqxy = EQ(x, y);
    final Node eqyx = EQ(y, x);

    final Node allTrue = AND(Nodes.TRUE, Nodes.TRUE, Nodes.TRUE);
    final Node singleExpr = AND(Nodes.TRUE, eqxy, Nodes.TRUE);
    final Node singleFalse = AND(Nodes.TRUE, Nodes.TRUE, Nodes.TRUE, eqxy, Nodes.FALSE, eqxy);

    Assert.assertTrue(equalNodes(Transformer.standardize(allTrue), Nodes.TRUE));
    Assert.assertTrue(equalNodes(Transformer.standardize(singleFalse), Nodes.FALSE));

    final Node stdSingle = Transformer.standardize(singleExpr);
    Assert.assertTrue(equalNodes(stdSingle, eqyx) || equalNodes(stdSingle, eqxy));
  }

  @Test
  public void filterDuplicatedEqualities() {
    final NodeVariable x = newVariable("x");
    final NodeVariable y = newVariable("y");
    final Node eqxy = EQ(x, y);
    final Node eqyx = EQ(y, x);

    final Node multiExpr = AND(eqxy, Nodes.TRUE, Nodes.TRUE, Nodes.TRUE, eqxy, Nodes.TRUE, eqyx);

    final Node std = Transformer.standardize(multiExpr);
    Assert.assertTrue(equalNodes(std, eqxy) || equalNodes(std, eqyx));
  }

  @Test
  public void standardizeDisjunction() {
    final NodeVariable x = newVariable("x");
    final NodeVariable y = newVariable("y");
    final Node eqxy = EQ(x, y);

    final Node allFalse = OR(Nodes.FALSE, Nodes.FALSE, Nodes.FALSE);
    final Node singleExpr = OR(Nodes.FALSE, eqxy, Nodes.FALSE);
    final Node multiExpr = OR(eqxy, Nodes.FALSE, Nodes.FALSE, Nodes.FALSE, eqxy, Nodes.FALSE);
    final Node singleTrue = OR(Nodes.FALSE, Nodes.FALSE, Nodes.FALSE, eqxy, Nodes.TRUE, eqxy);

    Assert.assertTrue(Transformer.standardize(allFalse).toString().equals(Nodes.FALSE.toString()));
    Assert.assertTrue(Transformer.standardize(singleExpr).toString().equals(eqxy.toString()));
    Assert.assertTrue(Transformer.standardize(singleTrue).toString().equals(Nodes.TRUE.toString()));
    Assert.assertTrue(
        Transformer.standardize(multiExpr).toString().equals(OR(eqxy, eqxy).toString()));
  }

  @Test
  public void standardizeConjunctionTree() {
    final NodeVariable x = newVariable("x");
    final NodeVariable y = newVariable("y");

    final Node eqxy = EQ(x, y);
    final Node eqyx = EQ(y, x);

    final Node tree = AND(Nodes.TRUE, AND(Nodes.TRUE, AND(eqxy, Nodes.TRUE), Nodes.TRUE), Nodes.TRUE);
    final Node std = Transformer.standardize(tree);
    Assert.assertTrue(equalNodes(std, eqxy) || equalNodes(std, eqyx));
  }

  @Test
  public void standardizeDisjunctionTree() {
    final NodeVariable x = newVariable("x");
    final NodeVariable y = newVariable("y");
    final Node eqxy = EQ(x, y);

    final Node tree = OR(Nodes.FALSE, OR(Nodes.FALSE, OR(eqxy, Nodes.FALSE), Nodes.FALSE), Nodes.FALSE);
    Assert.assertTrue(equalNodes(Transformer.standardize(tree), eqxy));
  }

  private static boolean equalNodes(Node lhs, Node rhs) {
    return lhs.toString().equals(rhs.toString());
  }

  @Test
  public void standardizeEqualityWithImmediates() {
    final NodeValue ZERO = NodeValue.newInteger(0);
    final NodeValue ONE = NodeValue.newInteger(1);

    final NodeVariable x = newVariable("x");

    Assert.assertTrue(equalNodes(
        Transformer.standardize(EQ(ZERO, ZERO, ZERO)),
        Nodes.TRUE));

    Assert.assertTrue(equalNodes(
        Transformer.standardize(EQ(ZERO, ZERO, ONE, ZERO)),
        Nodes.FALSE));

    Assert.assertTrue(equalNodes(
        Transformer.standardize(EQ(x, ZERO, ZERO, ZERO)),
        EQ(ZERO, x)));

    Assert.assertTrue(equalNodes(
        Transformer.standardize(EQ(x, ZERO, Nodes.FALSE)),
        Nodes.FALSE));
  }

  @Test
  public void standardizeValueComparisons() {

    /* Integer values */
    final NodeValue ZERO = NodeValue.newInteger(0);
    final NodeValue ONE = NodeValue.newInteger(1);
    final NodeValue TWO = NodeValue.newInteger(2);

    /* 0 != 1 */
    Assert.assertTrue(equalNodes(Transformer.standardize(NOTEQ(ZERO, ONE)), Nodes.TRUE));

    /* 2 > 1 */
    Assert.assertTrue(equalNodes(Transformer.standardize(Nodes.greater(TWO, ONE)), Nodes.TRUE));

    /* 1 >= 0 */
    Assert.assertTrue(equalNodes(Transformer.standardize(GREATEREQ(ONE, ZERO)), Nodes.TRUE));

    /* 0 < 2 */
    Assert.assertTrue(equalNodes(Transformer.standardize(Nodes.less(ZERO, TWO)), Nodes.TRUE));

    /* 0 <= 1 */
    Assert.assertTrue(equalNodes(Transformer.standardize(LESSEQ(ZERO, ONE)), Nodes.TRUE));

    /* (1 >= 2) == false */
    Assert.assertTrue(equalNodes(Transformer.standardize(GREATEREQ(ONE, TWO)), Nodes.FALSE));
  }

  @Test
  public void standardizeIfThenElse() {
    final NodeVariable x = newVariable("x");
    final NodeVariable y = newVariable("y");

    final NodeOperation ifLess = Nodes.ite(Nodes.less(x, y), x, y);

    Assert.assertTrue(equalNodes(Transformer.standardize(Nodes.ite(Nodes.TRUE, x, y)), x));
    Assert.assertTrue(equalNodes(Transformer.standardize(Nodes.ite(Nodes.FALSE, x, y)), y));
    Assert.assertTrue(equalNodes(Transformer.standardize(ifLess), ifLess));
  }

  @Test
  public void equalityResolution() {
    final NodeVariable x = newVariable("x");
    final NodeValue eqValue = NodeValue.newInteger(0);
    final NodeValue neqValue = NodeValue.newInteger(-1);

    final Node expr = AND(EQ(x, eqValue), NOTEQ(x, neqValue));
    final Node std = Transformer.standardize(expr);

    Assert.assertTrue(equalNodes(std, EQ(x, eqValue)) || equalNodes(std, EQ(eqValue, x)));
  }

  @Test
  public void equalNotEqual() {
    final NodeVariable a = new NodeVariable("a", DataType.BIT_VECTOR(2));
    final NodeVariable b = new NodeVariable("b", DataType.BIT_VECTOR(2));
    final NodeValue zero = NodeValue.newBitVector(BitVector.valueOf(0, 2));
    
    final Node expr = AND(EQ(a, zero), Nodes.not(EQ(a, b, zero)));
    final Node std = Transformer.standardize(expr);
    Assert.assertTrue(ExprUtils.isSAT(expr) == ExprUtils.isSAT(std));
  }
}
