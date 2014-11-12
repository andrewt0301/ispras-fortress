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

package ru.ispras.fortress.transformer;

import org.junit.*;

import java.util.List;
import java.util.Collections;

import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.data.DataType;

import ru.ispras.fortress.expression.*;

public class SimpleTransformTestCase {
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

  private static NodeOperation OR(Node... args) {
    return new NodeOperation(StandardOperation.OR, args);
  }

  private static NodeOperation IMPL(Node... args) {
    return new NodeOperation(StandardOperation.IMPL, args);
  }

  private static NodeOperation NOT(Node node) {
    return new NodeOperation(StandardOperation.NOT, node);
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

    final Node booleanEquality = EQ(equality, NodeValue.newBoolean(true));
    final Node booleanInequality = EQ(NodeValue.newBoolean(false), EQ(x, y));

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

    final Node TRUE = NodeValue.newBoolean(true);
    final Node FALSE = NodeValue.newBoolean(false);

    final Node trueThenFalse = EQ(eqxy, TRUE, eqxz, FALSE);
    final Node falseThenTrue = EQ(FALSE, eqxy, eqxz, TRUE);

    final Node expectedEquality = AND(eqxy, eqxz, FALSE);
    final Node standardEquality = Transformer.standardize(trueThenFalse);

    final Node expectedInequality = AND(NOT(eqxy), NOT(eqxz), FALSE);
    final Node standardInequality = Transformer.standardize(falseThenTrue);

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

    final Node TRUE = NodeValue.newBoolean(true);
    final Node FALSE = NodeValue.newBoolean(false);

    final Node impl2 = IMPL(eqxy, eqxz);
    final Node impl3 = IMPL(eqxy, eqxz, eqyz);

    final Node std2 = Transformer.standardize(impl2);
    final Node std3 = Transformer.standardize(impl3);

    Assert.assertTrue(std2.toString().equals(OR(NOT(eqxy), eqxz).toString()));
    Assert.assertTrue(std3.toString().equals(
        OR(NOT(eqxy), NOT(eqxz), eqyz).toString()));
  }
}
