/*
 * Copyright 2017 ISP RAS (http://www.ispras.ru)
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
import ru.ispras.fortress.expression.ExprUtils;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeBinding;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.util.InvariantChecks;

import java.util.IdentityHashMap;
import java.util.Map;

public final class Reducer {
  private static final BindingRule     BINDING_RULE = new BindingRule();
  private static final VariableRule   VARIABLE_RULE = new VariableRule();
  private static final OperationRule OPERATION_RULE = new OperationRule();

  private static final Map<Enum<?>, TransformerRule> REDUCER_RULES =
      new IdentityHashMap<Enum<?>, TransformerRule>();

  static {
    REDUCER_RULES.put(Node.Kind.BINDING,     BINDING_RULE);
    REDUCER_RULES.put(Node.Kind.VARIABLE,   VARIABLE_RULE);
    REDUCER_RULES.put(Node.Kind.OPERATION, OPERATION_RULE);
  }

  private static class BindingRule implements TransformerRule {
    @Override
    public boolean isApplicable(final Node node) {
      if (node.getKind() != Node.Kind.BINDING) {
        return false;
      }

      final NodeBinding binding = (NodeBinding) node;
      return ExprUtils.isValue(binding.getExpression());
    }

    @Override
    public Node apply(final Node node) {
      final NodeBinding binding = (NodeBinding) node;
      return binding.getExpression();
    }
  }

  private static class VariableRule implements TransformerRule {
    private ValueProvider valueProvider;

    public void setValueProvider(final ValueProvider valueProvider) {
      this.valueProvider = valueProvider;
    }

    @Override
    public boolean isApplicable(final Node node) {
      if (!ExprUtils.isVariable(node)) {
        return false;
      }

      final NodeVariable variable = (NodeVariable) node;
      if (null != valueProvider &&
          null != valueProvider.getVariableValue(variable.getName())) {
        return true;
      }

      return variable.getVariable().hasValue();
    }

    @Override
    public Node apply(final Node node) {
      final NodeVariable variable = (NodeVariable) node;
      Data data = null;

      if (null != valueProvider) {
        data = valueProvider.getVariableValue(variable.getName());
      }

      if (null == data) {
        data = variable.getData();
      }

      return new NodeValue(data);
    }
  }

  private static class OperationRule implements TransformerRule {
    private CalculatorEngine calculatorEngine;

    public void setCalculatorEngine(final CalculatorEngine calculatorEngine) {
      this.calculatorEngine = calculatorEngine;
    }

    @Override
    public boolean isApplicable(final Node node) {
      if (node.getKind() != Node.Kind.OPERATION) {
        return false;
      }

      final NodeOperation operation = (NodeOperation) node;
      if (operation.getOperandCount() == 0) {
        return false;
      }

      for (final Node operand : operation.getOperands()) {
        if (!ExprUtils.isValue(operand)) {
          return false;
        }
      }

      return true;
    }

    @Override
    public Node apply(final Node node) {
      final NodeOperation operation = (NodeOperation) node;
      final Data[] values = new Data[operation.getOperandCount()];

      for (int index = 0; index < operation.getOperandCount(); ++index) {
        values[index] = ((NodeValue) operation.getOperand(index)).getData();
      }

      final Data result = null != calculatorEngine ?
          calculatorEngine.calculate(operation.getOperationId(), values) :
          Calculator.calculate(operation.getOperationId(), values);

      return new NodeValue(result);
    }
  }

  public static Node reduce(
      final CalculatorEngine calculatorEngine,
      final ValueProvider valueProvider,
      final ReduceOptions options,
      final Node expression) {
    InvariantChecks.checkNotNull(options);
    InvariantChecks.checkNotNull(expression);

    OPERATION_RULE.setCalculatorEngine(calculatorEngine);
    VARIABLE_RULE.setValueProvider(valueProvider);

    try {
      final NodeTransformer nodeTransformer = new NodeTransformer(REDUCER_RULES);
      nodeTransformer.walk(expression);
      return nodeTransformer.getResult().iterator().next();
    } finally {
      OPERATION_RULE.setCalculatorEngine(null);
      VARIABLE_RULE.setValueProvider(null);
    }
  }

  public static Node reduce(
      final ValueProvider valueProvider,
      final Node expression) {
    return reduce(null, valueProvider, ReduceOptions.NEW_INSTANCE, expression);
  }
}
