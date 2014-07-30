/*
 * Copyright (c) 2013 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * OperationReducer.java, Nov 7, 2013 10:54:37 AM Andrei Tatarnikov
 */

package ru.ispras.fortress.transformer;

import ru.ispras.fortress.calculator.Calculator;
import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.expression.*;

public class OperationReducer
{
    private final static String UNKNOWN_ELEMENT = "Unknown syntax element kind: %s";

    private final NodeExpr    operation;
    private final ReduceOptions  options;
    private final Node[]        operands;

    private boolean hasValueOperandsOnly;
    private boolean      updatedOperands;

    public OperationReducer(NodeExpr operation, ReduceOptions options)
    {
        this.operation  = operation;
        this.options    = options;
        this.operands   = copyOperands(operation);

        analyzeOperands();
    }

    public Node reduce()
    {
        if (hasValueOperandsOnly)
        {
            final NodeValue result =
                calculate(operation.getOperationId(), operands);

            if (null != result)
                return result;
        }

        if (updatedOperands)
            return new NodeExpr(operation.getOperationId(), operands);

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

                case EXPR:
                    final Node reduced =
                        Transformer.reduce(options, (NodeExpr) o);

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

    private NodeValue calculate(Enum<?> operation, Node[] operands)
    {
        final Data[] dataOperands = new Data[operands.length];

        for (int index = 0; index < operands.length; ++index)
        {
            final NodeValue value = ((NodeValue) operands[index]);
            dataOperands[index] = value.getData();
        }

        if (!Calculator.isSupported(operation, dataOperands))
            return null;

        final Data result = Calculator.calculate(operation, dataOperands);
        return new NodeValue(result);
    }

    private static Node[] copyOperands(NodeExpr operation)
    {
        final Node[] operands = 
            new Node[operation.getOperandCount()];

        for (int index = 0; index < operands.length; ++index)
            operands[index] = operation.getOperand(index);

        return operands;
    }
}
