/*
 * Copyright 2013-2014 ISP RAS (http://www.ispras.ru)
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

import static ru.ispras.fortress.util.InvariantChecks.checkNotNull;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.DataTypeId;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.StandardOperation;

/**
 * The StandardFunctionFactory class provides factory methods for creating functions that are
 * responsible for performing special custom operations (first of all, some specific operations from
 * HDL).
 * 
 * @author Sergey Smolov (ssedai@ispras.ru)
 */

public final class StandardFunctionFactory {
  private StandardFunctionFactory() {}

  private static final String OPERAND_NAME = "x";
  private static final String LEFT_NAME = "x";
  private static final String RIGHT_NAME = "y";

  public static Function makeAbs(Enum<?> id, DataType operandType) {
    checkNotNull(id);
    checkNotNull(operandType);
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

    final NodeOperation body = new NodeOperation(
      StandardOperation.ITE,
      new NodeOperation(StandardOperation.GREATEREQ, operandNode, new NodeValue(zeroData)),
      operandNode,
      new NodeOperation(StandardOperation.MINUS, operandNode)
    );

    return new Function(id, returnType, body, operand);
  }

  public static Function makeMin(Enum<?> id, DataType leftType, DataType rightType) {
    checkNotNull(id);
    checkNotNull(leftType);
    checkNotNull(rightType);

    checkEqualTypes(leftType, rightType);
    checkLogicNumeric(LEFT_NAME, leftType);
    checkLogicNumeric(RIGHT_NAME, rightType);

    final DataType returnType = leftType;

    final Variable left = new Variable(LEFT_NAME, leftType);
    final Variable right = new Variable(RIGHT_NAME, rightType);

    final Node leftNode = new NodeVariable(left);
    final Node rightNode = new NodeVariable(right);

    final NodeOperation body = new NodeOperation(
      StandardOperation.ITE,
      new NodeOperation(StandardOperation.GREATEREQ, leftNode, rightNode),
      rightNode,
      leftNode
    );

    return new Function(id, returnType, body, left, right);
  }

  public static Function makeMax(Enum<?> id, DataType leftType, DataType rightType) {
    checkNotNull(id);
    checkNotNull(leftType);
    checkNotNull(rightType);

    checkEqualTypes(leftType, rightType);
    checkLogicNumeric(LEFT_NAME, leftType);
    checkLogicNumeric(RIGHT_NAME, rightType);

    final DataType returnType = leftType;

    final Variable left = new Variable(LEFT_NAME, leftType);
    final Variable right = new Variable(RIGHT_NAME, rightType);

    final Node leftNode = new NodeVariable(left);
    final Node rightNode = new NodeVariable(right);

    final NodeOperation body = new NodeOperation(
      StandardOperation.ITE,
      new NodeOperation(StandardOperation.GREATEREQ, leftNode, rightNode),
      leftNode,
      rightNode
    );

    return new Function(id, returnType, body, left, right);
  }

  public static Function makeBVANDR(Enum<?> id, DataType operandType) {
    checkNotNull(id);
    checkNotNull(operandType);
    checkBitVector(OPERAND_NAME, operandType);

    final Variable operand = new Variable(OPERAND_NAME, operandType);

    final NodeOperation body =
      new NodeOperation(StandardOperation.ITE, makeBVEqualsAllOnes(operand), BIT_TRUE, BIT_FALSE);

    return new Function(id, BIT_BOOL, body, operand);
  }

  public static Function makeBVNANDR(Enum<?> id, DataType operandType) {
    checkNotNull(id);
    checkNotNull(operandType);
    checkBitVector(OPERAND_NAME, operandType);

    final Variable operand = new Variable(OPERAND_NAME, operandType);

    final NodeOperation body =
      new NodeOperation(StandardOperation.ITE, makeBVEqualsAllOnes(operand), BIT_FALSE, BIT_TRUE);

    return new Function(id, BIT_BOOL, body, operand);
  }

  public static Function makeBVORR(Enum<?> id, DataType operandType) {
    checkNotNull(id);
    checkNotNull(operandType);
    checkBitVector(OPERAND_NAME, operandType);

    final Variable operand = new Variable(OPERAND_NAME, operandType);

    final NodeOperation body =
      new NodeOperation(StandardOperation.ITE, makeBVEqualsAllZeros(operand), BIT_FALSE, BIT_TRUE);

    return new Function(id, BIT_BOOL, body, operand);
  }

  public static Function makeBVNORR(Enum<?> id, DataType operandType) {
    checkNotNull(id);
    checkNotNull(operandType);
    checkBitVector(OPERAND_NAME, operandType);

    final Variable operand = new Variable(OPERAND_NAME, operandType);

    final NodeOperation body =
      new NodeOperation(StandardOperation.ITE, makeBVEqualsAllZeros(operand), BIT_TRUE, BIT_FALSE);

    return new Function(id, BIT_BOOL, body, operand);
  }

  public static Function makeBVXORR(Enum<?> id, DataType operandType) {
    checkNotNull(id);
    checkNotNull(operandType);
    checkBitVector(OPERAND_NAME, operandType);

    final Variable operand = new Variable(OPERAND_NAME, operandType);

    final int size = operand.getType().getSize();
    final Node body = makeBVRecursizeXOR(new NodeVariable(operand), size, size);

    return new Function(id, BIT_BOOL, body, operand);
  }

  public static Function makeBVXNORR(Enum<?> id, DataType operandType) {
    checkNotNull(id);
    checkNotNull(operandType);
    checkBitVector(OPERAND_NAME, operandType);

    final Variable operand = new Variable(OPERAND_NAME, operandType);

    final int size = operand.getType().getSize();

    final Node body = new NodeOperation(
      StandardOperation.BVNOT, makeBVRecursizeXOR(new NodeVariable(operand), size, size));

    return new Function(id, BIT_BOOL, body, operand);
  }

  private static void checkEqualTypes(DataType leftType, DataType rightType) {
    if (leftType.equals(rightType)) {
      return;
    }

    throw new IllegalArgumentException(
      String.format(ERR_UNEQUAL_ARG_TYPES, leftType, rightType));
  }

  private static void checkLogicNumeric(String name, DataType type) {
    final DataTypeId typeId = type.getTypeId();

    if ((DataTypeId.LOGIC_INTEGER == typeId) || (DataTypeId.LOGIC_REAL == typeId)) {
      return;
    }

    throw new IllegalArgumentException(String.format(ERR_UNSUPPORTED_ARG_TYPE,
      name, type, DataTypeId.LOGIC_INTEGER + " and " + DataTypeId.LOGIC_REAL));
  }

  private static void checkBitVector(String name, DataType type) {
    final DataTypeId typeId = type.getTypeId();
    if (DataTypeId.BIT_VECTOR == typeId) {
      return;
    }

    throw new IllegalArgumentException(String.format(ERR_UNSUPPORTED_ARG_TYPE,
      name, type, DataTypeId.BIT_VECTOR));
  }

  private static final Node makeBVRecursizeXOR(Node source, int size, int partSize) {
    if (1 == size) {
      return source;
    }

    assert 2 <= partSize : 
      String.format("Invalid part size: %s. Minimal part size is 2 bits.", partSize);

    if (2 == partSize) {
      return makeBVTwoBitPartXOR(source, size);
    }

    final int newPartSize = partSize / 2 + partSize % 2;
    final Node shiftLeftPart = new NodeValue(Data.newBitVector(newPartSize, size));

    final Node maskForRightPart = new NodeOperation(
      StandardOperation.BVLSHR,
      new NodeOperation(StandardOperation.BVNOT, new NodeValue(Data.newBitVector(0, size))),
      new NodeValue(Data.newBitVector(size - newPartSize, size))
    );

    final Node newSource = new NodeOperation(
      StandardOperation.BVXOR,
      new NodeOperation(StandardOperation.BVLSHR, source, shiftLeftPart),
      new NodeOperation(StandardOperation.BVAND, source, maskForRightPart)
    );

    return makeBVRecursizeXOR(newSource, size, newPartSize);
  }

  private static final Node makeBVTwoBitPartXOR(Node source, int size) {
    final NodeValue TWO_ZEROS = new NodeValue(DataType.BIT_VECTOR(size).valueOf("00", 2));
    final NodeValue TWO_ONES = new NodeValue(DataType.BIT_VECTOR(size).valueOf("11", 2));

    return new NodeOperation(
      StandardOperation.ITE,
      new NodeOperation(StandardOperation.OR,
        new NodeOperation(StandardOperation.EQ, source, TWO_ZEROS),
        new NodeOperation(StandardOperation.EQ, source, TWO_ONES)
      ),
      BIT_FALSE,
      BIT_TRUE
    );
  }

  private static final Node makeBVEqualsAllZeros(Variable operand) {
    final DataType operandType = operand.getType();

    final NodeVariable operandNode = new NodeVariable(operand);
    final NodeValue zeroNode = new NodeValue(Data.newBitVector(0, operandType.getSize()));

    return new NodeOperation(StandardOperation.EQ, operandNode, zeroNode);
  }

  private static final Node makeBVEqualsAllOnes(Variable operand) {
    final DataType operandType = operand.getType();

    final NodeVariable operandNode = new NodeVariable(operand);
    final NodeValue zeroNode = new NodeValue(Data.newBitVector(0, operandType.getSize()));

    return new NodeOperation(
      StandardOperation.EQ,
      operandNode,
      new NodeOperation(StandardOperation.BVNOT, zeroNode)
    );
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
