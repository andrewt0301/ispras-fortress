/*
 * Copyright (c) 2011 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * SMTTextBuilder.java, Dec 20, 2011 12:24:52 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver.engine.z3;

import java.io.*;
import java.util.*;


import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.*;
import ru.ispras.fortress.solver.SolverOperation;
import ru.ispras.fortress.solver.function.Function;

import static ru.ispras.fortress.solver.engine.z3.SMTStrings.*;

/**
 * The SMTTextBuilder class implements logic that generates SMT-LIB code from a syntax structure.
 * Generated code is saved to a text file. 
 * 
 * @author Andrei Tatarnikov
 */

final class SMTTextBuilder implements Visitor
{
    private final Map<Enum<?>, SolverOperation> operations;
    private final Iterable<Variable>             variables;

    private List<StringBuilder>         formulas = new LinkedList<StringBuilder>();
    private FunctionDefinitionBuilders functions = new FunctionDefinitionBuilders();

    private StringBuilder currentBuilder = null;
    private int        functionCallDepth = 0;

    /**
     * Creates an instance of a SMT text builder.
     * @param operations Operation dictionary.
     */

    SMTTextBuilder(Iterable<Variable> variables, Map<Enum<?>, SolverOperation> operations)
    {
        this.operations = operations;
        this.variables = variables;
    }

    private StringBuilder getCurrentBuilder()
    {
        assert null != currentBuilder : "The current builder is not assigned.";
        return currentBuilder;
    }
    
    private void appendToCurrent(String s)
    {
        assert null != currentBuilder : "The current builder is not assigned.";
        currentBuilder.append(s);
    }

    private void setCurrentBuilder(StringBuilder builder)
    {
        currentBuilder = builder;
    }

    /**
     * Saves the generated SMT-LIB representation to a text file.
     *  
     * @param fileName The name of the target file.
     * @throws IOException if failed to create the output file.
     */

    public void saveToFile(String fileName) throws IOException
    {
        PrintWriter out = null;
        try 
        {
            final FileWriter outFile = new FileWriter(fileName);
            out = new PrintWriter(outFile);

            final StringBuilder variablesListBuilder = new StringBuilder();
            for (Variable variable : variables)
            {
                // Variables that have values don't need declarations 
                // because their values are used in expression as constants.
                if (!variable.hasValue())
                {
                    out.printf(sDECLARE_CONST,
                        variable.getName(), textForType(variable.getData().getType()));

                    variablesListBuilder.append(sSPACE);
                    variablesListBuilder.append(variable.getName());
                }
            }

            for (StringBuilder builder : functions.getBuilders())
                out.printf(sDEFINE_FUN, builder.toString());

            for (StringBuilder builder : formulas)
                out.printf(sASSERT, builder.toString());

            out.println(sCHECK_SAT);
            out.printf(sGET_VALUE, variablesListBuilder.toString());
            out.println(sEXIT);
        }
        finally
        {
            if (null != out)
                out.close();
        }
    }

    private void addFunctionDefinition(Enum<?> id, Function function)
    {
        if (functions.isDefined(id))
            return;

        final StringBuilder builder = new StringBuilder();

        builder.append(id.name());
        builder.append(sSPACE);

        // Forms the parameter list.
        builder.append(sBRACKET_OPEN);
        for (int index = 0; index < function.getParameterCount(); ++index)
        {
            final Variable param = function.getParameter(index);
            builder.append(String.format(sPARAM_DEF, param.getName(), textForType(param.getData().getType()))); 
        }
        builder.append(sBRACKET_CLOSE);

        // Appends the return type
        builder.append(sSPACE);
        builder.append(textForType(function.getReturnType()));

        // Forms the function body
        final StringBuilder previousBuilder = getCurrentBuilder();
        setCurrentBuilder(builder);

        functions.addEntry(id, functionCallDepth, builder);

        if (0 == functionCallDepth)
            functions.beginCallTree();

        functionCallDepth++;

        final Walker walker = new Walker(this);
        walker.visitNode(function.getBody());

        functionCallDepth--;

        if (0 == functionCallDepth)
            functions.endCallTree();

        setCurrentBuilder(previousBuilder);
    }

    @Override
    public void onRootBegin()
    {
        final StringBuilder builder = new StringBuilder();
        formulas.add(builder);
        setCurrentBuilder(builder);
    }

    @Override
    public void onRootEnd()
    {
        setCurrentBuilder(null);
    }

    @Override
    public void onExprBegin(NodeExpr expr)
    {
        final Enum<?> op = expr.getOperationId();
        
        if (!operations.containsKey(op))
            throw new IllegalArgumentException("Unsupported operation: " + op);

        final SolverOperation operation = operations.get(op);

        if (operation.isCustom())
            addFunctionDefinition(op, operation.getFunction());

        appendToCurrent(sSPACE);

        if (expr.getOperandCount() > 0)
            appendToCurrent(sBRACKET_OPEN);

        if (StandardOperation.isParametric(op))
        {
            appendToCurrent(sBRACKET_OPEN);
            appendToCurrent(sUNDERLINE);
            appendToCurrent(sSPACE);
        }

        appendToCurrent(operation.getText());
    }

    @Override
    public void onExprEnd(NodeExpr expr)
    {
        if (expr.getOperandCount() > 0)
            appendToCurrent(sBRACKET_CLOSE);
    }

    @Override
    public void onOperandBegin(NodeExpr expr, Node node, int index)
    {
        // Do nothing.
    }

    @Override
    public void onOperandEnd(NodeExpr expr, Node node, int index)
    {
        if ((0 == index) && StandardOperation.isParametric(expr.getOperationId()))
            appendToCurrent(sBRACKET_CLOSE);
    }

    @Override
    public void onValue(NodeValue value)
    {
        onValue(value.getData());
    }

    private void onValue(Data data)
    {
        appendToCurrent(sSPACE);
        appendToCurrent(textForData(data));
    }

    @Override
    public void onVariable(NodeVariable variable)
    {
        if (variable.getData().hasValue())
        {
            onValue(variable.getData());
        }
        else
        {
            appendToCurrent(sSPACE);
            appendToCurrent(variable.getName());
        }
    }
}

final class FunctionDefinitionBuilders
{
    private final Set<Enum<?>>                      hashes;
    private final List<StringBuilder>              entries;
    private final Map<Integer, List<StringBuilder>>  queue;

    private boolean callTreeStarted = false;

    private static final class ReverseComparator implements Comparator<Integer>
    {
        public int compare(Integer o1, Integer o2)
        {
            return -o1.compareTo(o2);
        }
    }

    public FunctionDefinitionBuilders()
    {
        this.hashes  = new HashSet<Enum<?>>();
        this.entries = new ArrayList<StringBuilder>();
        this.queue   = new TreeMap<Integer, List<StringBuilder>>(new ReverseComparator());
    }

    public void beginCallTree()
    {
        assert !callTreeStarted;
        callTreeStarted = true;
    }

    public void endCallTree()
    {
        assert callTreeStarted;

        for (List<StringBuilder> level : queue.values())
            for (StringBuilder entry : level)
                entries.add(entry);

        queue.clear();
        callTreeStarted = true;
    }

    public boolean isDefined(Enum<?> opId)
    {
        return hashes.contains(opId);
    }

    public void addEntry(Enum<?> key, Integer depth, StringBuilder entry)
    {
        assert !hashes.contains(key) : "The function is already defined."; 

        hashes.add(key);

        final List<StringBuilder> level;
        if (queue.containsKey(depth))
        {
            level = queue.get(depth);
        }
        else
        {
            level = new ArrayList<StringBuilder>();
            queue.put(depth, level);
        }

        level.add(entry);
    }

    public Iterable<StringBuilder> getBuilders()
    {
        return entries;
    }
}