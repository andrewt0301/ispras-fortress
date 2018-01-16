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

import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.types.bitvector.BitVector;
import ru.ispras.fortress.expression.ExprUtils;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeBinding;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.StandardOperation;

import java.util.List;
import java.util.Collections;

public class SimpleTransformTestCase {
  private static final NodeValue TRUE = NodeValue.newBoolean(true);
  private static final NodeValue FALSE = NodeValue.newBoolean(false);

  private static NodeVariable createVariable(String name) {
    final Variable var = new Variable(name, DataType.INTEGER);
    return new NodeVariable(var);
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

  private static NodeOperation GREATER(Node... args) {
    return new NodeOperation(StandardOperation.GREATER, args);
  }

  private static NodeOperation GREATEREQ(Node... args) {
    return new NodeOperation(StandardOperation.GREATEREQ, args);
  }

  private static NodeOperation LESS(Node... args) {
    return new NodeOperation(StandardOperation.LESS, args);
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

  private static NodeOperation NOT(Node node) {
    return new NodeOperation(StandardOperation.NOT, node);
  }

  private static NodeOperation ITE(Node cond, Node ifTrue, Node ifFalse) {
    final Node[] operands = { cond, ifTrue, ifFalse };
    return new NodeOperation(StandardOperation.ITE, operands);
  }

  private static NodeBinding singleBinding(NodeVariable variable, Node value, Node expr) {
    final List<NodeBinding.BoundVariable> bindings =
      Collections.singletonList(NodeBinding.bindVariable(variable, value));

    return new NodeBinding(expr, bindings);
  }

  @Test
  public void substituteSingleVariable() {
    final Node a = createVariable("a");
    final Node b = createVariable("b");
    final Node c = createVariable("c");

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
    final NodeVariable a = createVariable("a");
    final NodeVariable x = createVariable("x");
    final NodeVariable y = createVariable("y");

    final Node let = singleBinding(a, PLUS(x, y), PLUS(x, a));
    final Node unchanged = Transformer.substitute(let, "a", x);

    Assert.assertTrue(unchanged.toString().equals(let.toString()));

    final Node changed = Transformer.substitute(let, "x", y);
    final Node expected = singleBinding(a, PLUS(y, y), PLUS(y, a));

    Assert.assertTrue(changed.toString().equals(expected.toString()));
  }

  @Test
  public void substituteBinding() {
    final NodeVariable a = createVariable("a");
    final NodeVariable x = createVariable("x");
    final NodeVariable y = createVariable("y");

    final NodeBinding let = singleBinding(a, PLUS(x, y), PLUS(x, a));
    final Node unrolled = Transformer.substituteBinding(let);
    final Node expected = PLUS(x, PLUS(x, y));

    Assert.assertTrue(unrolled.toString().equals(expected.toString()));
  }

  @Test
  public void substituteAllBindings() {
    final NodeVariable a = createVariable("a");
    final NodeVariable x = createVariable("x");
    final NodeVariable y = createVariable("y");

    final NodeBinding letA = singleBinding(a, PLUS(x, y), PLUS(x, a));
    final NodeBinding letY = singleBinding(y, PLUS(x, x), letA);

    final Node unrolled = Transformer.substituteAllBindings(PLUS(y, letY));
    final Node expected = PLUS(y, PLUS(x, PLUS(x, PLUS(x, x))));

    Assert.assertTrue(unrolled.toString().equals(expected.toString()));
  }

  @Test
  public void standardizeBooleanEquality() {
    final NodeVariable x = createVariable("x");
    final NodeVariable y = createVariable("y");

    final Node equality = EQ(x, y);

    final Node booleanEquality = EQ(equality, TRUE);
    final Node booleanInequality = EQ(FALSE, EQ(x, y));

    final Node standardEquality = Transformer.standardize(booleanEquality);
    final Node standardInequality = Transformer.standardize(booleanInequality);

    Assert.assertTrue(standardEquality.toString().equals(equality.toString()));
    Assert.assertTrue(standardInequality.toString().equals(NOT(equality).toString()));
  }

  @Test
  public void standardizeChainedBooleanEquality() {
    final NodeVariable x = createVariable("x");
    final NodeVariable y = createVariable("y");
    final NodeVariable z = createVariable("z");

    final Node eqxy = EQ(x, y);
    final Node eqxz = EQ(x, z);

    final Node equalsTrue = EQ(eqxy, TRUE, eqxz);
    final Node equalsFalse = EQ(FALSE, eqxy, eqxz);

    final Node expectedEquality = EQ(z, y, x);
    final Node standardEquality = Transformer.standardize(equalsTrue);

    final Node expectedInequality = AND(NOT(eqxy), NOT(eqxz));
    final Node standardInequality = Transformer.standardize(equalsFalse);

    Assert.assertTrue(standardEquality.toString().equals(expectedEquality.toString()));
    Assert.assertTrue(standardInequality.toString().equals(expectedInequality.toString()));
  }

  @Test
  public void standardizeImplication() {
    final NodeVariable x = createVariable("x");
    final NodeVariable y = createVariable("y");
    final NodeVariable z = createVariable("z");

    final Node eqxy = EQ(x, y);
    final Node eqxz = EQ(x, z);
    final Node eqyz = EQ(y, z);

    final Node impl2 = IMPL(eqxy, eqxz);
    final Node impl3 = IMPL(eqxy, eqxz, eqyz);

    final Node std2 = Transformer.standardize(impl2);
    final Node std3 = Transformer.standardize(impl3);

    Assert.assertTrue(std2.toString().equals(OR(NOT(eqxy), eqxz).toString()));
    Assert.assertTrue(std3.toString().equals(
        OR(NOT(eqxy), NOT(eqxz), eqyz).toString()));
  }

  @Test
  public void standardizeConjunction() {
    final NodeVariable x = createVariable("x");
    final NodeVariable y = createVariable("y");
    final Node eqxy = EQ(x, y);
    final Node eqyx = EQ(y, x);

    final Node allTrue = AND(TRUE, TRUE, TRUE);
    final Node singleExpr = AND(TRUE, eqxy, TRUE);
    final Node singleFalse = AND(TRUE, TRUE, TRUE, eqxy, FALSE, eqxy);

    Assert.assertTrue(equalNodes(Transformer.standardize(allTrue), TRUE));
    Assert.assertTrue(equalNodes(Transformer.standardize(singleFalse), FALSE));

    final Node stdSingle = Transformer.standardize(singleExpr);
    Assert.assertTrue(equalNodes(stdSingle, eqyx) || equalNodes(stdSingle, eqxy));
  }

  @Test
  public void filterDuplicatedEqualities() {
    final NodeVariable x = createVariable("x");
    final NodeVariable y = createVariable("y");
    final Node eqxy = EQ(x, y);
    final Node eqyx = EQ(y, x);

    final Node multiExpr = AND(eqxy, TRUE, TRUE, TRUE, eqxy, TRUE, eqyx);

    final Node std = Transformer.standardize(multiExpr);
    Assert.assertTrue(equalNodes(std, eqxy) || equalNodes(std, eqyx));
  }

  @Test
  public void standardizeDisjunction() {
    final NodeVariable x = createVariable("x");
    final NodeVariable y = createVariable("y");
    final Node eqxy = EQ(x, y);

    final Node allFalse = OR(FALSE, FALSE, FALSE);
    final Node singleExpr = OR(FALSE, eqxy, FALSE);
    final Node multiExpr = OR(eqxy, FALSE, FALSE, FALSE, eqxy, FALSE);
    final Node singleTrue = OR(FALSE, FALSE, FALSE, eqxy, TRUE, eqxy);

    Assert.assertTrue(Transformer.standardize(allFalse).toString().equals(FALSE.toString()));
    Assert.assertTrue(Transformer.standardize(singleExpr).toString().equals(eqxy.toString()));
    Assert.assertTrue(Transformer.standardize(singleTrue).toString().equals(TRUE.toString()));
    Assert.assertTrue(
      Transformer.standardize(multiExpr).toString().equals(
        OR(eqxy, eqxy).toString()));
  }

  @Test
  public void standardizeConjunctionTree() {
    final NodeVariable x = createVariable("x");
    final NodeVariable y = createVariable("y");

    final Node eqxy = EQ(x, y);
    final Node eqyx = EQ(y, x);

    final Node tree = AND(TRUE, AND(TRUE, AND(eqxy, TRUE), TRUE), TRUE);
    final Node std = Transformer.standardize(tree);
    Assert.assertTrue(equalNodes(std, eqxy) || equalNodes(std, eqyx));
  }

  @Test
  public void standardizeDisjunctionTree() {
    final NodeVariable x = createVariable("x");
    final NodeVariable y = createVariable("y");
    final Node eqxy = EQ(x, y);

    final Node tree = OR(FALSE, OR(FALSE, OR(eqxy, FALSE), FALSE), FALSE);
    Assert.assertTrue(equalNodes(Transformer.standardize(tree), eqxy));
  }

  private static boolean equalNodes(Node lhs, Node rhs) {
    return lhs.toString().equals(rhs.toString());
  }

  @Test
  public void standardizeEqualityWithImmediates() {
    final NodeValue ZERO = NodeValue.newInteger(0);
    final NodeValue ONE = NodeValue.newInteger(1);

    final NodeVariable x = createVariable("x");

    Assert.assertTrue(equalNodes(
        Transformer.standardize(EQ(ZERO, ZERO, ZERO)),
        TRUE));

    Assert.assertTrue(equalNodes(
        Transformer.standardize(EQ(ZERO, ZERO, ONE, ZERO)),
        FALSE));

    Assert.assertTrue(equalNodes(
        Transformer.standardize(EQ(x, ZERO, ZERO, ZERO)),
        EQ(ZERO, x)));

    Assert.assertTrue(equalNodes(
        Transformer.standardize(EQ(x, ZERO, FALSE)),
        FALSE));
  }

  @Test
  public void standardizeValueComparisons() {

    /* Integer values */
    final NodeValue ZERO = NodeValue.newInteger(0);
    final NodeValue ONE = NodeValue.newInteger(1);
    final NodeValue TWO = NodeValue.newInteger(2);

    /* 0 != 1 */
    Assert.assertTrue(equalNodes(Transformer.standardize(NOTEQ(ZERO, ONE)), TRUE));

    /* 2 > 1 */
    Assert.assertTrue(equalNodes(Transformer.standardize(GREATER(TWO, ONE)), TRUE));

    /* 1 >= 0 */
    Assert.assertTrue(equalNodes(Transformer.standardize(GREATEREQ(ONE, ZERO)), TRUE));

    /* 0 < 2 */
    Assert.assertTrue(equalNodes(Transformer.standardize(LESS(ZERO, TWO)), TRUE));

    /* 0 <= 1 */
    Assert.assertTrue(equalNodes(Transformer.standardize(LESSEQ(ZERO, ONE)), TRUE));

    /* (1 >= 2) == false */
    Assert.assertTrue(equalNodes(Transformer.standardize(GREATEREQ(ONE, TWO)), FALSE));
  }

  @Test
  public void standardizeIfThenElse() {
    final NodeVariable x = createVariable("x");
    final NodeVariable y = createVariable("y");

    final NodeOperation ifLess = ITE(LESS(x, y), x, y);

    Assert.assertTrue(equalNodes(Transformer.standardize(ITE(TRUE, x, y)), x));
    Assert.assertTrue(equalNodes(Transformer.standardize(ITE(FALSE, x, y)), y));
    Assert.assertTrue(equalNodes(Transformer.standardize(ifLess), ifLess));
  }

  @Test
  public void equalityResolution() {
    final NodeVariable x = createVariable("x");
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
    
    final Node expr = AND(EQ(a, zero), NOT(EQ(a, b, zero)));
    final Node std = Transformer.standardize(expr);
    Assert.assertTrue(ExprUtils.isSAT(expr) == ExprUtils.isSAT(std));
  }
}
