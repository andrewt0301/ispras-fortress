/*
 * Copyright (c) 2012 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * $Id: SolverResultChecker.java, Jan 13, 2012 12:47:08 PM andrewt Exp $
 */

package ru.ispras.fortress.solver.common;

import java.util.Iterator;
import org.junit.Assert;

import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.solver.SolverResult;

public class SolverResultChecker
{    
    public static void check(SolverResult solverResult, Iterable<Variable> expectedVariables)
    {
        checkErrors(solverResult.getErrors());

        Assert.assertTrue("Failed to solve the constraint. Status: " +
           solverResult.getStatus(), solverResult.getStatus() == SolverResult.Status.SAT);

        final Iterator<Variable> expectedVariableIterator = expectedVariables.iterator();
        final Iterator<Variable> variableIterator = solverResult.getVariables().iterator();

        while(expectedVariableIterator.hasNext() && variableIterator.hasNext())
        {
            final Variable expectedVariable = expectedVariableIterator.next();
            final Variable variable = variableIterator.next();

            Assert.assertTrue(
                String.format("Unexpected variable name. '%s' vs '%s'",
                    variable.getName(),
                    expectedVariable.getName()),
                    variable.getName().equals(expectedVariable.getName())
            );

            Assert.assertTrue(
                String.format("Unexpected variable type. '%s' vs '%s'",
                    variable.getData().getType().toString(),
                    expectedVariable.getData().getType().toString()),
                    variable.getData().getType().equals(expectedVariable.getData().getType())
            );

            Assert.assertTrue(
                String.format("Unexpected value of the %s variable: '%s', expected: '%s'",
                    variable.getName(),
                    variable.getData().getValue(),
                    expectedVariable.getData().getValue()),
                    variable.getData().getValue().equals(expectedVariable.getData().getValue())
            );
        }

        Assert.assertTrue("Wrong variable number", !expectedVariableIterator.hasNext() && !variableIterator.hasNext());
    }

    private static void checkErrors(Iterable<String> errors)
    {
        Iterator<String> errorIterator = errors.iterator();

        if (!errorIterator.hasNext())
            return;

        StringBuilder errorStringBuilder = new StringBuilder();
        errorStringBuilder.append("Errors occured:");

        while (errorIterator.hasNext())
        {
            errorStringBuilder.append("\r\n");
            errorStringBuilder.append(errorIterator.next());
        }

        Assert.fail(errorStringBuilder.toString());
    }
}
