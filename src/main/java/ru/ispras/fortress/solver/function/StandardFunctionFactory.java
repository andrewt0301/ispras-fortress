/*
 * Copyright 2013-2018 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.solver.function;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.DataTypeId;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.Nodes;
import ru.ispras.fortress.util.InvariantChecks;

/**
 * The {@link StandardFunctionFactory} class provides factory methods for creating functions
 * that are responsible for performing special custom operations (first of all, some specific
 * operations from HDL).
 *
 * @author <a href="mailto:ssedai@ispras.ru">Sergey Smolov</a>
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public final class StandardFunctionFactory {
  private StandardFunctionFactory() {}

  private static final String OPERAND_NAME = "x";
  private static final String LEFT_NAME = "x";
  private static final String RIGHT_NAME = "y";

  public static Function abs(final Enum<?> id, final DataType operandType) {
    InvariantChecks.checkNotNull(id);
    InvariantChecks.checkNotNull(operandType);

    checkLogicNumeric(OPERAND_NAME, operandType);

    final DataType returnType = operandType;
    final Variable operand = new Variable(OPERAND_NAME, operandType);
    final Node operandNode = new NodeVariable(operand);

    final Data zeroData;
    switch (returnType.getTypeId()) {
      case LOGIC_INTEGER:
        zeroData = Data.newInteger(0);
        break;

      case LOGIC_REAL:
        zeroData = Data.newReal(0);
        break;

      default:
        zeroData = null;
        assert false;
    }

    final NodeOperation body = Nodes.ite(
        Nodes.greatereq(operandNode, new NodeValue(zeroData)),
        operandNode,
        Nodes.minus(operandNode)
        );

    return new Function(id, returnType, body, operand);
  }

  public static Function min(
      final Enum<?> id,
      final DataType leftType,
      final DataType rightType) {
    InvariantChecks.checkNotNull(id);
    InvariantChecks.checkNotNull(leftType);
    InvariantChecks.checkNotNull(rightType);

    checkEqualTypes(leftType, rightType);
    checkLogicNumeric(LEFT_NAME, leftType);
    checkLogicNumeric(RIGHT_NAME, rightType);

    final DataType returnType = leftType;

    final Variable left = new Variable(LEFT_NAME, leftType);
    final Variable right = new Variable(RIGHT_NAME, rightType);

    final Node leftNode = new NodeVariable(left);
    final Node rightNode = new NodeVariable(right);

    final NodeOperation body = Nodes.ite(
        Nodes.greatereq(leftNode, rightNode),
        rightNode,
        leftNode
        );

    return new Function(id, returnType, body, left, right);
  }

  public static Function max(
      final Enum<?> id,
      final DataType leftType,
      final DataType rightType) {
    InvariantChecks.checkNotNull(id);
    InvariantChecks.checkNotNull(leftType);
    InvariantChecks.checkNotNull(rightType);

    checkEqualTypes(leftType, rightType);
    checkLogicNumeric(LEFT_NAME, leftType);
    checkLogicNumeric(RIGHT_NAME, rightType);

    final DataType returnType = leftType;

    final Variable left = new Variable(LEFT_NAME, leftType);
    final Variable right = new Variable(RIGHT_NAME, rightType);

    final Node leftNode = new NodeVariable(left);
    final Node rightNode = new NodeVariable(right);

    final NodeOperation body = Nodes.ite(
        Nodes.greatereq(leftNode, rightNode),
        leftNode,
        rightNode
        );

    return new Function(id, returnType, body, left, right);
  }

  public static Function bvandr(final Enum<?> id, final DataType operandType) {
    InvariantChecks.checkNotNull(id);
    InvariantChecks.checkNotNull(operandType);

    checkBitVector(OPERAND_NAME, operandType);

    final Variable operand = new Variable(OPERAND_NAME, operandType);
    final NodeOperation body = Nodes.ite(newBvEqualsAllOnes(operand), BIT_TRUE, BIT_FALSE);

    return new Function(id, BIT_BOOL, body, operand);
  }

  public static Function bvnandr(final Enum<?> id, final DataType operandType) {
    InvariantChecks.checkNotNull(id);
    InvariantChecks.checkNotNull(operandType);

    checkBitVector(OPERAND_NAME, operandType);

    final Variable operand = new Variable(OPERAND_NAME, operandType);
    final NodeOperation body = Nodes.ite(newBvEqualsAllOnes(operand), BIT_FALSE, BIT_TRUE);

    return new Function(id, BIT_BOOL, body, operand);
  }

  public static Function bvorr(final Enum<?> id, final DataType operandType) {
    InvariantChecks.checkNotNull(id);
    InvariantChecks.checkNotNull(operandType);

    checkBitVector(OPERAND_NAME, operandType);

    final Variable operand = new Variable(OPERAND_NAME, operandType);
    final NodeOperation body = Nodes.ite(newBvEqualsAllZeros(operand), BIT_FALSE, BIT_TRUE);

    return new Function(id, BIT_BOOL, body, operand);
  }

  public static Function bvnorr(final Enum<?> id, final DataType operandType) {
    InvariantChecks.checkNotNull(id);
    InvariantChecks.checkNotNull(operandType);

    checkBitVector(OPERAND_NAME, operandType);

    final Variable operand = new Variable(OPERAND_NAME, operandType);
    final NodeOperation body = Nodes.ite(newBvEqualsAllZeros(operand), BIT_TRUE, BIT_FALSE);

    return new Function(id, BIT_BOOL, body, operand);
  }

  public static Function bvxorr(final Enum<?> id, final DataType operandType) {
    InvariantChecks.checkNotNull(id);
    InvariantChecks.checkNotNull(operandType);
    checkBitVector(OPERAND_NAME, operandType);

    final Variable operand = new Variable(OPERAND_NAME, operandType);

    final int size = operand.getType().getSize();
    final Node body = newBvRecursizeXor(new NodeVariable(operand), size, size);

    return new Function(id, BIT_BOOL, body, operand);
  }

  public static Function bvxnorr(final Enum<?> id, final DataType operandType) {
    InvariantChecks.checkNotNull(id);
    InvariantChecks.checkNotNull(operandType);
    checkBitVector(OPERAND_NAME, operandType);

    final Variable operand = new Variable(OPERAND_NAME, operandType);

    final int size = operand.getType().getSize();
    final Node body = Nodes.bvnot(newBvRecursizeXor(new NodeVariable(operand), size, size));

    return new Function(id, BIT_BOOL, body, operand);
  }

  private static void checkEqualTypes(final DataType leftType, final DataType rightType) {
    if (leftType.equals(rightType)) {
      return;
    }

    throw new IllegalArgumentException(
      String.format(ERR_UNEQUAL_ARG_TYPES, leftType, rightType));
  }

  private static void checkLogicNumeric(final String name, final DataType type) {
    final DataTypeId typeId = type.getTypeId();

    if (DataTypeId.LOGIC_INTEGER == typeId || DataTypeId.LOGIC_REAL == typeId) {
      return;
    }

    throw new IllegalArgumentException(String.format(ERR_UNSUPPORTED_ARG_TYPE,
        name, type, DataTypeId.LOGIC_INTEGER + " and " + DataTypeId.LOGIC_REAL));
  }

  private static void checkBitVector(final String name, final DataType type) {
    final DataTypeId typeId = type.getTypeId();
    if (DataTypeId.BIT_VECTOR == typeId) {
      return;
    }

    throw new IllegalArgumentException(
        String.format(ERR_UNSUPPORTED_ARG_TYPE, name, type, DataTypeId.BIT_VECTOR));
  }

  private static Node newBvRecursizeXor(
      final Node source, 
      final int size, 
      final int partSize) {
    if (1 == size) {
      return source;
    }

    assert 2 <= partSize : 
      String.format("Invalid part size: %s. Minimal part size is 2 bits.", partSize);

    if (2 == partSize) {
      return newBvTwoBitPartXor(source, size);
    }

    final int newPartSize = partSize / 2 + partSize % 2;
    final Node shiftLeftPart = new NodeValue(Data.newBitVector(newPartSize, size));

    final Node maskForRightPart = Nodes.bvlshr(
        Nodes.bvnot(new NodeValue(Data.newBitVector(0, size))),
        new NodeValue(Data.newBitVector(size - newPartSize, size))
        );

    final Node newSource = Nodes.bvxor(
        Nodes.bvlshr(source, shiftLeftPart),
        Nodes.bvand(source, maskForRightPart)
        );

    return newBvRecursizeXor(newSource, size, newPartSize);
  }

  private static Node newBvTwoBitPartXor(final Node source, final int size) {
    final NodeValue TWO_ZEROS = new NodeValue(DataType.BIT_VECTOR(size).valueOf("00", 2));
    final NodeValue TWO_ONES = new NodeValue(DataType.BIT_VECTOR(size).valueOf("11", 2));

    return Nodes.ite(
        Nodes.or(Nodes.eq(source, TWO_ZEROS), Nodes.eq(source, TWO_ONES)),
        BIT_FALSE,
        BIT_TRUE
        );
  }

  private static Node newBvEqualsAllZeros(final Variable operand) {
    final DataType operandType = operand.getType();

    final NodeVariable operandNode = new NodeVariable(operand);
    final NodeValue zeroNode = new NodeValue(Data.newBitVector(0, operandType.getSize()));

    return Nodes.eq(operandNode, zeroNode);
  }

  private static Node newBvEqualsAllOnes(final Variable operand) {
    final DataType operandType = operand.getType();

    final NodeVariable operandNode = new NodeVariable(operand);
    final NodeValue zeroNode = new NodeValue(Data.newBitVector(0, operandType.getSize()));

    return Nodes.eq(operandNode, Nodes.bvnot(zeroNode));
  }

  private static final int BIT_BOOL_SIZE = 1;
  private static final DataType BIT_BOOL = DataType.BIT_VECTOR(BIT_BOOL_SIZE);
  private static final NodeValue BIT_TRUE = new NodeValue(Data.newBitVector(1, BIT_BOOL_SIZE));
  private static final NodeValue BIT_FALSE = new NodeValue(Data.newBitVector(0, BIT_BOOL_SIZE));

  private static final String ERR_UNEQUAL_ARG_TYPES =
      "Arguments have unequal types: %s and %s.";

  private static final String ERR_UNSUPPORTED_ARG_TYPE =
      "Argument %s (%s) has an unsupported type. Expected types: %s.";
}
