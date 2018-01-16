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

package ru.ispras.fortress.solver.constraint;

import org.junit.Assert;

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeBinding;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;

import java.util.Iterator;

public final class ConstraintEqualityChecker {
  private ConstraintEqualityChecker() {}

  public static void check(Constraint expected, Constraint actual) {
    Assert.assertNotNull(expected);
    Assert.assertNotNull(actual);
    Assert.assertFalse("The same object", expected == actual);

    Assert.assertTrue("Constraint names do not match.",
        expected.getName().equals(actual.getName()));
    Assert.assertTrue("Constraint kinds.", expected.getKind() == actual.getKind());
    Assert.assertTrue("Constraint descriptions do not match.",
        expected.getDescription().equals(actual.getDescription()));

    check((Formulas) expected.getInnerRep(), (Formulas) actual.getInnerRep());
  }

  public static void check(Formulas expected, Formulas actual) {
    Assert.assertNotNull(expected);
    Assert.assertNotNull(actual);
    Assert.assertFalse("The same object", expected == actual);

    Assert.assertNotNull(expected.exprs());
    Assert.assertNotNull(actual.exprs());
    Assert.assertFalse("The same object", expected.exprs() == actual.exprs());

    final Iterator<Node> expectedIterator = expected.exprs().iterator();
    final Iterator<Node> actualIterator = actual.exprs().iterator();

    while (expectedIterator.hasNext() && actualIterator.hasNext()) {
      check(expectedIterator.next(), actualIterator.next());
    }

    Assert.assertTrue(
        "The numbers of formulas are different.",
        expectedIterator.hasNext() == actualIterator.hasNext());
  }

  public static void check(NodeOperation expected, NodeOperation actual) {
    Assert.assertNotNull(expected);
    Assert.assertNotNull(actual);
    Assert.assertFalse("The same object", expected == actual);

    Assert.assertTrue("Invalid element ID.", expected.getKind() == Node.Kind.OPERATION);
    Assert.assertTrue("Invalid element ID.", actual.getKind() == Node.Kind.OPERATION);
    Assert.assertTrue("Different operation IDs.",
        expected.getOperationId().equals(actual.getOperationId()));

    // TODO: Temporary requirement. Once the getDataType method is implemented to return a proper
    // value
    // this code must be replaced with a proper check.
    // Assert.assertNull(expected.getDataType());
    // Assert.assertNull(actual.getDataType());

    int operandIndex = 0;
    while (operandIndex < expected.getOperandCount()) {
      if ((null != expected.getOperand(operandIndex))
          && (null != actual.getOperand(operandIndex))) {
        check(expected.getOperand(operandIndex), actual.getOperand(operandIndex));
      }

      ++operandIndex;
    }
  }

  public static void check(NodeBinding expected, NodeBinding actual) {
    Assert.assertNotNull(expected);
    Assert.assertNotNull(actual);
    Assert.assertFalse("The same object", expected == actual);

    Assert.assertTrue("Invalid element ID.", expected.getKind() == Node.Kind.BINDING);
    Assert.assertTrue("Invalid element ID.", actual.getKind() == Node.Kind.BINDING);
    Assert.assertTrue("Different number of bound variables.",
        expected.getBindings().size() == actual.getBindings().size());

    for (int i = 0; i < expected.getBindings().size(); ++i) {
      Assert.assertTrue("Different binding order.",
          getBoundName(expected, i).equals(getBoundName(actual, i)));
      check(getBoundValue(expected, i), getBoundValue(actual, i));
    }
  }

  public static void check(NodeVariable expected, NodeVariable actual) {
    Assert.assertNotNull(expected);
    Assert.assertNotNull(actual);
    Assert.assertFalse("The same object", expected == actual);

    Assert.assertTrue("Invalid node kind.", expected.getKind() == Node.Kind.VARIABLE);
    Assert.assertTrue("Invalid node kind.", actual.getKind() == Node.Kind.VARIABLE);

    Assert.assertTrue("Variable names do not match.", expected.getName().equals(actual.getName()));

    check(expected.getData().getType(), actual.getData().getType());
    if (!((null == expected.getValue()) && (null == actual.getValue()))) {
      Assert.assertTrue(
          "Variable values do not match.", expected.getValue().equals(actual.getValue()));
    }
  }

  public static void check(NodeValue expected, NodeValue actual) {
    Assert.assertNotNull(expected);
    Assert.assertNotNull(actual);
    Assert.assertFalse("The same object", expected == actual);

    Assert.assertTrue("Invalid element ID.", expected.getKind() == Node.Kind.VALUE);
    Assert.assertTrue("Invalid element ID.", actual.getKind() == Node.Kind.VALUE);
    check(expected.getData().getType(), actual.getData().getType());
    Assert.assertTrue("Values do not match.", expected.getValue().equals(actual.getValue()));
  }

  public static void check(Node expected, Node actual) {
    Assert.assertNotNull(expected);
    Assert.assertNotNull(actual);

    Assert.assertFalse("The same object", expected == actual);
    Assert.assertTrue("Different element IDs.", expected.getKind() == actual.getKind());

    switch (expected.getKind()) {
      case VALUE:
        check((NodeValue) expected, (NodeValue) actual);
        break;

      case VARIABLE:
        check((NodeVariable) expected, (NodeVariable) actual);
        break;

      case OPERATION:
        check((NodeOperation) expected, (NodeOperation) actual);
        break;

      case BINDING:
        check((NodeBinding) expected, (NodeBinding) actual);
        break;

      default:
        Assert.fail("Unknown element type.");
        break;
    }
  }

  public static void check(DataType expected, DataType actual) {
    Assert.assertNotNull(expected);
    Assert.assertNotNull(actual);

    Assert.assertTrue("Data type IDs do not match.", expected.getTypeId() == actual.getTypeId());
    Assert.assertTrue("Data type sizes do not match.", expected.getSize() == actual.getSize());
  }

  private static String getBoundName(NodeBinding node, int index) {
    return node.getBindings().get(index).getVariable().getName();
  }

  private static Node getBoundValue(NodeBinding node, int index) {
    return node.getBindings().get(index).getValue();
  }
}
