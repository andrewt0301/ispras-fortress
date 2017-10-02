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

import ru.ispras.fortress.calculator.CalculatorEngine;
import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.expression.ExprUtils;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeBinding;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.util.InvariantChecks;

final class Reducer {
  public static Node reduce(
      final CalculatorEngine engine,
      final ValueProvider valueProvider,
      final ReduceOptions options,
      final Node expression) {
    InvariantChecks.checkNotNull(options);
    InvariantChecks.checkNotNull(expression);

    if (ExprUtils.isVariable(expression)) {
      return reduceVariable(valueProvider, (NodeVariable) expression);
    }

    if (expression.getKind() == Node.Kind.BINDING) {
      return reduceBinding(engine, valueProvider, options, (NodeBinding) expression);
    }

    if (expression.getKind() == Node.Kind.OPERATION) {
      return reduceOperation(engine, valueProvider, options, (NodeOperation) expression);
    }

    return expression;
  }

  private static Node reduceVariable(
      final ValueProvider valueProvider,
      final NodeVariable variable) {
    InvariantChecks.checkNotNull(variable);

    if (null != valueProvider) {
      final Data data = valueProvider.getVariableValue(variable.getName());
      if (null != data) {
        return new NodeValue(data);
      }
    }

    if (variable.getVariable().hasValue()) {
      return new NodeValue(variable.getData());
    }

    return variable;
  }

  private static Node reduceBinding(
      final CalculatorEngine engine,
      final ValueProvider valueProvider,
      final ReduceOptions options,
      final NodeBinding binding) {
    InvariantChecks.checkNotNull(binding);

    final Node reduced = reduce(engine, valueProvider, options, binding.getExpression());
    if (reduced == null || reduced == binding.getExpression()) {
      return binding;
    }

    if (ExprUtils.isValue(reduced)) {
      return reduced;
    }

    return binding.bindTo(reduced);
  }

  private static Node reduceOperation(
      final CalculatorEngine engine,
      final ValueProvider valueProvider,
      final ReduceOptions options,
      final NodeOperation operation) {
    InvariantChecks.checkNotNull(operation);
    // TODO Auto-generated method stub
    return null;
  }
}
