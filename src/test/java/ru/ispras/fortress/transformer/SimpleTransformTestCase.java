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

public class SimpleTransformTestCase {
  private static NodeVariable newVariable(final String name) {
    return new NodeVariable(name, DataType.INTEGER);
  }

  private static NodeBinding singleBinding(
      final NodeVariable variable,
      final Node value,
      final Node expr) {
    return new NodeBinding(
        expr, Collections.singletonList(NodeBinding.bindVariable(variable, value)));
  }

  private static NodeOperation impl(final Node... args) {
    return new NodeOperation(StandardOperation.IMPL, args);
  }

  @Test
  public void substituteSingleVariable() {
    final Node a = newVariable("a");
    final Node b = newVariable("b");
    final Node c = newVariable("c");

    // (a = b + c)
    final Node expr = Nodes.eq(a, Nodes.add(b, c));
    final Node firstExpected = Nodes.eq(a, Nodes.add(a, c));
    final Node firstPass = Transformer.substitute(expr, "b", a);
    Assert.assertEquals(firstExpected, firstPass);

    final Node secondExpected = Nodes.eq(c, Nodes.add(c, c));
    final Node secondPass = Transformer.substitute(firstPass, "a", c);
    Assert.assertEquals(secondExpected, secondPass);
  }

  @Test
  public void substituteWithinBinding() {
    final NodeVariable a = newVariable("a");
    final NodeVariable x = newVariable("x");
    final NodeVariable y = newVariable("y");

    final Node let = singleBinding(a, Nodes.add(x, y), Nodes.add(x, a));
    final Node unchanged = Transformer.substitute(let, "a", x);

    Assert.assertEquals(unchanged, let);

    final Node changed = Transformer.substitute(let, "x", y);
    final Node expected = singleBinding(a, Nodes.add(y, y), Nodes.add(y, a));

    Assert.assertEquals(expected, changed);
  }

  @Test
  public void substituteBinding() {
    final NodeVariable a = newVariable("a");
    final NodeVariable x = newVariable("x");
    final NodeVariable y = newVariable("y");

    final NodeBinding let = singleBinding(a, Nodes.add(x, y), Nodes.add(x, a));
    final Node unrolled = Transformer.substituteBinding(let);
    final Node expected = Nodes.add(x, Nodes.add(x, y));

    Assert.assertEquals(expected, unrolled);
  }

  @Test
  public void substituteAllBindings() {
    final NodeVariable a = newVariable("a");
    final NodeVariable x = newVariable("x");
    final NodeVariable y = newVariable("y");

    final NodeBinding letA = singleBinding(a, Nodes.add(x, y), Nodes.add(x, a));
    final NodeBinding letY = singleBinding(y, Nodes.add(x, x), letA);

    final Node unrolled = Transformer.substituteAllBindings(Nodes.add(y, letY));
    final Node expected = Nodes.add(y, Nodes.add(x, Nodes.add(x, Nodes.add(x, x))));

    Assert.assertEquals(unrolled, expected);
  }

  @Test
  public void standardizeBooleanEquality() {
    final NodeVariable x = newVariable("x");
    final NodeVariable y = newVariable("y");

    final Node equality = Nodes.eq(x, y);

    final Node booleanEquality = Nodes.eq(equality, Nodes.TRUE);
    final Node booleanInequality = Nodes.eq(Nodes.FALSE, Nodes.eq(x, y));

    final Node standardEquality = Transformer.standardize(booleanEquality);
    final Node standardInequality = Transformer.standardize(booleanInequality);

    Assert.assertEquals(standardEquality, equality);
    Assert.assertEquals(standardInequality, Nodes.not(equality));
  }

  @Test
  public void standardizeChainedBooleanEquality() {
    final NodeVariable x = newVariable("x");
    final NodeVariable y = newVariable("y");
    final NodeVariable z = newVariable("z");

    final Node eqxy = Nodes.eq(x, y);
    final Node eqxz = Nodes.eq(x, z);

    final Node equalsTrue = Nodes.eq(eqxy, Nodes.TRUE, eqxz);
    final Node equalsFalse = Nodes.eq(Nodes.FALSE, eqxy, eqxz);

    final Node expectedEquality = Nodes.eq(z, y, x);
    final Node standardEquality = Transformer.standardize(equalsTrue);

    final Node expectedInequality = Nodes.and(Nodes.not(eqxy), Nodes.not(eqxz));
    final Node standardInequality = Transformer.standardize(equalsFalse);

    Assert.assertEquals(expectedEquality, standardEquality);
    Assert.assertEquals(expectedInequality, standardInequality);
  }

  @Test
  public void standardizeImplication() {
    final NodeVariable x = newVariable("x");
    final NodeVariable y = newVariable("y");
    final NodeVariable z = newVariable("z");

    final Node eqxy = Nodes.eq(x, y);
    final Node eqxz = Nodes.eq(x, z);
    final Node eqyz = Nodes.eq(y, z);

    final Node impl2 = impl(eqxy, eqxz);
    final Node impl3 = impl(eqxy, eqxz, eqyz);

    final Node std2 = Transformer.standardize(impl2);
    final Node std3 = Transformer.standardize(impl3);

    Assert.assertTrue(std2.toString().equals(Nodes.or(Nodes.not(eqxy), eqxz).toString()));
    Assert.assertTrue(std3.toString().equals(
        Nodes.or(Nodes.not(eqxy), Nodes.not(eqxz), eqyz).toString()));
  }

  @Test
  public void standardizeConjunction() {
    final NodeVariable x = newVariable("x");
    final NodeVariable y = newVariable("y");
    final Node eqxy = Nodes.eq(x, y);
    final Node eqyx = Nodes.eq(y, x);

    final Node allTrue = Nodes.and(Nodes.TRUE, Nodes.TRUE, Nodes.TRUE);
    final Node singleExpr = Nodes.and(Nodes.TRUE, eqxy, Nodes.TRUE);
    final Node singleFalse = Nodes.and(Nodes.TRUE, Nodes.TRUE, Nodes.TRUE, eqxy, Nodes.FALSE, eqxy);

    Assert.assertTrue(equalNodes(Transformer.standardize(allTrue), Nodes.TRUE));
    Assert.assertTrue(equalNodes(Transformer.standardize(singleFalse), Nodes.FALSE));

    final Node stdSingle = Transformer.standardize(singleExpr);
    Assert.assertTrue(equalNodes(stdSingle, eqyx) || equalNodes(stdSingle, eqxy));
  }

  @Test
  public void filterDuplicatedEqualities() {
    final NodeVariable x = newVariable("x");
    final NodeVariable y = newVariable("y");
    final Node eqxy = Nodes.eq(x, y);
    final Node eqyx = Nodes.eq(y, x);

    final Node multiExpr = Nodes.and(
        eqxy,
        Nodes.TRUE,
        Nodes.TRUE,
        Nodes.TRUE,
        eqxy,
        Nodes.TRUE,
        eqyx);

    final Node std = Transformer.standardize(multiExpr);
    Assert.assertTrue(equalNodes(std, eqxy) || equalNodes(std, eqyx));
  }

  @Test
  public void standardizeDisjunction() {
    final NodeVariable x = newVariable("x");
    final NodeVariable y = newVariable("y");
    final Node eqxy = Nodes.eq(x, y);

    final Node allFalse = Nodes.or(Nodes.FALSE, Nodes.FALSE, Nodes.FALSE);
    final Node singleExpr = Nodes.or(Nodes.FALSE, eqxy, Nodes.FALSE);
    final Node multiExpr = Nodes.or(eqxy, Nodes.FALSE, Nodes.FALSE, Nodes.FALSE, eqxy, Nodes.FALSE);
    final Node singleTrue = Nodes.or(Nodes.FALSE, Nodes.FALSE, Nodes.FALSE, eqxy, Nodes.TRUE, eqxy);

    Assert.assertTrue(Transformer.standardize(allFalse).toString().equals(Nodes.FALSE.toString()));
    Assert.assertTrue(Transformer.standardize(singleExpr).toString().equals(eqxy.toString()));
    Assert.assertTrue(Transformer.standardize(singleTrue).toString().equals(Nodes.TRUE.toString()));
    Assert.assertTrue(
        Transformer.standardize(multiExpr).toString().equals(Nodes.or(eqxy, eqxy).toString()));
  }

  @Test
  public void standardizeConjunctionTree() {
    final NodeVariable x = newVariable("x");
    final NodeVariable y = newVariable("y");

    final Node eqxy = Nodes.eq(x, y);
    final Node eqyx = Nodes.eq(y, x);

    final Node tree = Nodes.and(
        Nodes.TRUE,
        Nodes.and(Nodes.TRUE, Nodes.and(eqxy, Nodes.TRUE), Nodes.TRUE),
        Nodes.TRUE);

    final Node std = Transformer.standardize(tree);
    Assert.assertTrue(equalNodes(std, eqxy) || equalNodes(std, eqyx));
  }

  @Test
  public void standardizeDisjunctionTree() {
    final NodeVariable x = newVariable("x");
    final NodeVariable y = newVariable("y");
    final Node eqxy = Nodes.eq(x, y);

    final Node tree = Nodes.or(
        Nodes.FALSE,
        Nodes.or(Nodes.FALSE, Nodes.or(eqxy, Nodes.FALSE), Nodes.FALSE),
        Nodes.FALSE);

    Assert.assertTrue(equalNodes(Transformer.standardize(tree), eqxy));
  }

  private static boolean equalNodes(final Node lhs, final Node rhs) {
    return lhs.equals(rhs);
  }

  @Test
  public void standardizeEqualityWithImmediates() {
    final NodeValue zero = NodeValue.newInteger(0);
    final NodeValue one = NodeValue.newInteger(1);

    final NodeVariable x = newVariable("x");

    Assert.assertTrue(equalNodes(
        Transformer.standardize(Nodes.eq(zero, zero, zero)),
        Nodes.TRUE));

    Assert.assertTrue(equalNodes(
        Transformer.standardize(Nodes.eq(zero, zero, one, zero)),
        Nodes.FALSE));

    Assert.assertTrue(equalNodes(
        Transformer.standardize(Nodes.eq(x, zero, zero, zero)),
        Nodes.eq(zero, x)));

    Assert.assertTrue(equalNodes(
        Transformer.standardize(Nodes.eq(x, zero, Nodes.FALSE)),
        Nodes.FALSE));
  }

  @Test
  public void standardizeValueComparisons() {
    /* Integer values */
    final NodeValue zero = NodeValue.newInteger(0);
    final NodeValue one = NodeValue.newInteger(1);
    final NodeValue two = NodeValue.newInteger(2);

    /* 0 != 1 */
    Assert.assertTrue(equalNodes(Transformer.standardize(Nodes.noteq(zero, one)), Nodes.TRUE));

    /* 2 > 1 */
    Assert.assertTrue(equalNodes(Transformer.standardize(Nodes.greater(two, one)), Nodes.TRUE));

    /* 1 >= 0 */
    Assert.assertTrue(equalNodes(Transformer.standardize(Nodes.greatereq(one, zero)), Nodes.TRUE));

    /* 0 < 2 */
    Assert.assertTrue(equalNodes(Transformer.standardize(Nodes.less(zero, two)), Nodes.TRUE));

    /* 0 <= 1 */
    Assert.assertTrue(equalNodes(Transformer.standardize(Nodes.lesseq(zero, one)), Nodes.TRUE));

    /* (1 >= 2) == false */
    Assert.assertTrue(equalNodes(Transformer.standardize(Nodes.greatereq(one, two)), Nodes.FALSE));
  }

  @Test
  public void standardizeIfThenElse() {
    final NodeVariable x = newVariable("x");
    final NodeVariable y = newVariable("y");

    final NodeOperation ifLess = Nodes.ite(Nodes.less(x, y), x, y);

    Assert.assertEquals(Transformer.standardize(Nodes.ite(Nodes.TRUE, x, y)), x);
    Assert.assertEquals(Transformer.standardize(Nodes.ite(Nodes.FALSE, x, y)), y);
    Assert.assertEquals(Transformer.standardize(ifLess), ifLess);
  }

  @Test
  public void equalityResolution() {
    final NodeVariable x = newVariable("x");
    final NodeValue eqValue = NodeValue.newInteger(0);
    final NodeValue neqValue = NodeValue.newInteger(-1);

    final Node expr = Nodes.and(Nodes.eq(x, eqValue), Nodes.noteq(x, neqValue));
    final Node std = Transformer.standardize(expr);

    Assert.assertTrue(
        equalNodes(std, Nodes.eq(x, eqValue)) || equalNodes(std, Nodes.eq(eqValue, x)));
  }

  @Test
  public void equalNotEqual() {
    final NodeVariable a = new NodeVariable("a", DataType.bitVector(2));
    final NodeVariable b = new NodeVariable("b", DataType.bitVector(2));
    final NodeValue zero = NodeValue.newBitVector(BitVector.valueOf(0, 2));
    
    final Node expr = Nodes.and(Nodes.eq(a, zero), Nodes.not(Nodes.eq(a, b, zero)));
    final Node std = Transformer.standardize(expr);
    Assert.assertTrue(ExprUtils.isSat(expr) == ExprUtils.isSat(std));
  }
}
