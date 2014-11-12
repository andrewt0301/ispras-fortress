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

package ru.ispras.fortress.transformer;

import ru.ispras.fortress.calculator.Calculator;
import ru.ispras.fortress.calculator.CalculatorEngine;
import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;

/**
 * The OperationReducer class implements constant expression evaluation. OperationReducer relies on
 * {@link ru.ispras.fortress.calculator.CalculatorEngine CalculatorEngine} to support different sets
 * of operations.
 */

final class OperationReducer {
  private final static String UNKNOWN_ELEMENT = "Unknown syntax element kind: %s";

  private final CalculatorEngine engine;

  private final NodeOperation operation;
  private final Node[] operands;
  private final ReduceOptions options;

  private boolean hasValueOperandsOnly;
  private boolean updatedOperands;

  /**
   * Create reducer configuration.
   * 
   * @param engine Calculator engine supporting required set of operations.
   * @param operation Expression to be reduced.
   * @param options Reduction policy configuration.
   */

  public OperationReducer(CalculatorEngine engine, NodeOperation operation, ReduceOptions options) {
    if (null == operation) {
      throw new NullPointerException();
    }

    if (null == options) {
      throw new NullPointerException();
    }

    this.engine = engine;
    this.operation = operation;
    this.operands = copyOperands(operation);
    this.options = options;

    analyzeOperands();
  }

  /**
   * Run reduction on stored expression.
   * 
   * @return Reduced expression.
   */

  public Node reduce() {
    if (hasValueOperandsOnly) {
      final NodeValue result = calculate(engine, operation.getOperationId(), operands);

      if (null != result) {
        return result;
      }
    }

    if (updatedOperands) {
      return new NodeOperation(operation.getOperationId(), operands);
    }

    return operation;
  }

  /**
   * Collect required information about operands in stored operation. Checks if operation can be
   * evaluated, should operands be updated etc.
   */

  private void analyzeOperands() {
    hasValueOperandsOnly = true;
    updatedOperands = false;

    for (int index = 0; index < operation.getOperandCount(); ++index) {
      final Node o = operation.getOperand(index);
      switch (o.getKind()) {
        case VALUE:
          // Do nothing.
          break;

        case VARIABLE:
          hasValueOperandsOnly = false;
          break;

        case BINDING:
        case OPERATION:
          final Node reduced = Transformer.reduce(engine, options, o);

          if (reduced != o) {
            operands[index] = reduced;
            updatedOperands = true;
          }

          if (Node.Kind.VALUE != reduced.getKind()) {
            hasValueOperandsOnly = false;
          }

          break;

        default:
          hasValueOperandsOnly = false;
          assert false : String.format(UNKNOWN_ELEMENT, o.getKind().name());
          break;
      }
    }
  }

  /**
   * Check if calculator engine supports given operation.
   * 
   * @param engine Engine is to be checked. If null, default engine is used.
   * @param operation Operation to check support for.
   * @param operands Operation operands.
   * 
   * @return true if operation is supported.
   */

  private boolean isSupported(CalculatorEngine engine, Enum<?> operation, Data[] operands) {
    if (engine != null) {
      return engine.isSupported(operation, operands);
    }

    return Calculator.isSupported(operation, operands);
  }

  /**
   * Evaluate operation with given data operands.
   * 
   * @param engine Engine is to be used in evaluation. If null, default engine is used.
   * @param operation Operation to evaluate.
   * @param operands Operation operands.
   * 
   * @return Data instance for operation result.
   */

  private Data calculateData(CalculatorEngine engine, Enum<?> operation, Data[] operands) {
    if (engine != null) {
      return engine.calculate(operation, operands);
    }

    return Calculator.calculate(operation, operands);
  }

  /**
   * Evaluate operation with given node operands.
   * 
   * @param engine Engine is to be used in evaluation. If null, default engine is used.
   * @param operation Operation to evaluate.
   * @param operands Operation operands.
   * 
   * @return NodeValue instance for operation result.
   */

  private NodeValue calculate(CalculatorEngine engine, Enum<?> operation, Node[] operands) {
    final Data[] dataOperands = new Data[operands.length];

    for (int index = 0; index < operands.length; ++index) {
      final NodeValue value = ((NodeValue) operands[index]);
      dataOperands[index] = value.getData();
    }

    if (!isSupported(engine, operation, dataOperands)) {
      return null;
    }

    final Data result = calculateData(engine, operation, dataOperands);
    return new NodeValue(result);
  }

  /**
   * Helper method to extract operands from operation node.
   * 
   * @param operation Operation node to extract operands from.
   * @return Array of operand nodes.
   */

  private static Node[] copyOperands(NodeOperation operation) {
    final Node[] operands = new Node[operation.getOperandCount()];

    for (int index = 0; index < operands.length; ++index) {
      operands[index] = operation.getOperand(index);
    }

    return operands;
  }
}
