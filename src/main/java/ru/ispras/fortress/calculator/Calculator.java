/*
 * Copyright (c) 2013 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * Calculator.java, Nov 7, 2013 4:26:56 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.calculator;

import java.util.HashMap;
import java.util.Map;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.expression.StandardOperation;

/**
 * The Calculator class is responsible for performing calculations on an array of data objects 
 * using an extendable set of operations. It encapsulates a table of calculator engines each
 * implementing operations that belong to some logic group. Each group is represented by a
 * enumeration identifying operations it contains. The class of the enumeration is used
 * to identify engines implementing operations from the given group. It is possible to extend
 * functionality by registering custom engines implementing new group of operations. Also, you
 * can replace existing engines with custom engines if needed.      
 * 
 * @author Andrei Tatarnikov
 */

public final class Calculator
{
    private Calculator() {}

    /**
     * A singleton for the calculator engine that implements standard operations described
     * by the StandardOperation enumeration. 
     */

    public static final CalculatorEngine STANDARD;

    // Key: class of the operation group enumeration, value: engine implementing operations from the group.
    private static final Map<Class<? extends Enum<?>>, CalculatorEngine> engines =
        new HashMap<Class<? extends Enum<?>>, CalculatorEngine>(); 

    static
    {
        // Creates and registers an engine that performs calculation using standard operations. 

        final OperationGroup<StandardOperation> standardOperations =
            new OperationGroup<StandardOperation>();

        // Register operation for Int values. 
        standardOperations.registerOperations
        (
            StandardOperationsInt.dataTypeId(),
            StandardOperationsInt.operations()
        );

        STANDARD = standardOperations;
        registerEngine(StandardOperation.class, STANDARD);
    }

    /**
     * Registers a calculator engine that performs calculations using operations that belong
     * to the given operation group which is described with a corresponding enumeration.
     * The class of the enumeration serves as a key.
     * 
     * @param operationIdClass Class of the enumeration that identifies operations implemented
     * by the given calculator engine.
     * @param engine Calculator engine to be registered.
     * @return <code>true</code> if the engine was successfully registered and it had not been
     * previously registered or <code>false</code> if an engine identified by the specified class
     * had already been registered (in this case, it is replaced with a new engine).
     */

    public static boolean registerEngine(Class<? extends Enum<?>> operationIdClass, CalculatorEngine engine)
    {
        assert null != operationIdClass;
        assert null != engine;

        return null == engines.put(operationIdClass, engine);
    }

    /**
     * Returns the engine that performs calculations using a specific group of operations.
     * Operations that belong to a single group are identified with a corresponding enumeration.
     * The class of the enumeration serves as a key. If no such engine is registered <code>null</code>
     * is returned.
     * 
     * @param operationIdClass Class of the enumeration that identifies operations implemented
     * by the given engine.
     * @return Engine responsible for performing a specific group of operations or <code>null</code>
     * if no such engine is registered.
     */

    public static CalculatorEngine getEngine(Class<?> operationIdClass)
    {
        return engines.get(operationIdClass);
    }

    /**
     * Checks whether the specified operation is supported for the provided operands.
     * Class of the operation identifier, its value and operand types are taken into consideration.
     * 
     * @param operationId Operation identifier. Identifies an operation within a group.
     * @param operands Array of operands.
     * @return <code>true</code> if the operation is supported for the given operand types
     * or <code>false</code> otherwise.
     */

    public static boolean isSupported(Enum<?> operationId, Data[] operands)
    {
        final CalculatorEngine engine = getEngine(operationId.getClass());

        if (null == engine)
            return false;

        return engine.isSupported(operationId, operands);
    }

    /**
     * Performs calculation by applying the specified operation to the operands. If the operation
     * is not supported or its invariants are violated (e.g. operand types do not match) 
     * the UnsupportedOperationException runtime exception will be thrown.
     * 
     * @param operationId Operation identifier. Identifies an operation within a group.
     * @param operands Array of operands.
     * @return Data object holding the calculated value.
     */

    public static Data calculate(Enum<?> operationId, Data[] operands)
    {
        final CalculatorEngine engine = getEngine(operationId.getClass());

        if (null == engine)
        {
            throw new UnsupportedOperationException(
                String.format(MSG_UNSUPPORTED_GROUP_FRMT, operationId.getClass().getSimpleName()));
        }

        return engine.calculate(operationId, operands);
    }

    private static final String MSG_UNSUPPORTED_GROUP_FRMT =
         "The specified operation family is not supported: %s.";
}
