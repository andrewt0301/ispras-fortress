/*
 * Copyright (c) 2013 ISPRAS (www.ispras.ru)
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * OperationReducer.java, Nov 7, 2013 10:54:37 AM Andrei Tatarnikov
 * 
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not
 * use this file except in compliance with the License. You may obtain a copy of
 * the License at
 * 
 * http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations under
 * the License.
 */

package ru.ispras.fortress.transformer;

import ru.ispras.fortress.calculator.Calculator;
import ru.ispras.fortress.calculator.CalculatorEngine;
import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;

final class OperationReducer
{
    private final static String UNKNOWN_ELEMENT = 
        "Unknown syntax element kind: %s";

    private final CalculatorEngine engine;

    private final NodeOperation operation;
    private final Node[] operands;
    private final ReduceOptions options;

    private boolean hasValueOperandsOnly;
    private boolean updatedOperands;

    public OperationReducer(CalculatorEngine engine, NodeOperation operation, ReduceOptions options)
    {
        if (null == operation)
            throw new NullPointerException();

        if (null == options)
            throw new NullPointerException();

        this.engine = engine;
        this.operation = operation;
        this.operands = copyOperands(operation);
        this.options = options;

        analyzeOperands();
    }

    public Node reduce()
    {
        if (hasValueOperandsOnly)
        {
            final NodeValue result =
                calculate(engine, operation.getOperationId(), operands);

            if (null != result)
                return result;
        }

        if (updatedOperands)
            return new NodeOperation(operation.getOperationId(), operands);

        return operation;
    }

    private void analyzeOperands()
    {
        hasValueOperandsOnly = true;
        updatedOperands = false;

        for (int index = 0; index < operation.getOperandCount(); ++index)
        {
            final Node o = operation.getOperand(index); 
            switch (o.getKind())
            {
                case VALUE:
                    // Do nothing.
                    break;

                case VARIABLE:
                    hasValueOperandsOnly = false;
                    break;

                case BINDING:
                case OPERATION:
                    final Node reduced =
                        Transformer.reduce(engine, options, o);

                    if (reduced != o)
                    {
                        operands[index] = reduced;
                        updatedOperands = true;
                    }

                    if (Node.Kind.VALUE != reduced.getKind())
                        hasValueOperandsOnly = false;

                    break;

                default:
                    hasValueOperandsOnly = false;
                    assert false : String.format(UNKNOWN_ELEMENT, o.getKind().name());
                    break;
            }
        }
    }

    private boolean isSupported(CalculatorEngine engine, Enum<?> operation, Data[] operands)
    {
        if (engine != null) 
            return engine.isSupported(operation, operands);

        return Calculator.isSupported(operation, operands);
    }

    private Data calculateData(CalculatorEngine engine, Enum<?> operation, Data[] operands)
    {
        if (engine != null)
            return engine.calculate(operation, operands);

        return Calculator.calculate(operation, operands);
    }

    private NodeValue calculate(CalculatorEngine engine, Enum<?> operation, Node[] operands)
    {
        final Data[] dataOperands = new Data[operands.length];

        for (int index = 0; index < operands.length; ++index)
        {
            final NodeValue value = ((NodeValue) operands[index]);
            dataOperands[index] = value.getData();
        }

        if (!isSupported(engine, operation, dataOperands))
            return null;

        final Data result = calculateData(engine, operation, dataOperands);
        return new NodeValue(result);
    }

    private static Node[] copyOperands(NodeOperation operation)
    {
        final Node[] operands = 
            new Node[operation.getOperandCount()];

        for (int index = 0; index < operands.length; ++index)
            operands[index] = operation.getOperand(index);

        return operands;
    }
}
