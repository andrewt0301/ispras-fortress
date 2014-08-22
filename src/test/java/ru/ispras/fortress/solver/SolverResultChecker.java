/*
 * Copyright (c) 2014 ISPRAS (www.ispras.ru)
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * SolverResultChecker.java, Aug 22, 2014 6:34:56 PM Andrei Tatarnikov
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

package ru.ispras.fortress.solver;

import java.util.Iterator;
import java.util.TreeMap;
import org.junit.Assert;

import ru.ispras.fortress.data.Variable;

public final class SolverResultChecker
{   
    private SolverResultChecker() {}
    
    public static void check(SolverResult solverResult, Iterable<Variable> expectedVariables)
    {
        checkErrors(solverResult.getErrors());

        Assert.assertTrue("Failed to solve the constraint. Status: " +
           solverResult.getStatus(), solverResult.getStatus() == SolverResult.Status.SAT);

        final TreeMap<String, Variable> results = new TreeMap<String, Variable>();
        for (Variable v : solverResult.getVariables())
            results.put(v.getName(), v);

        final TreeMap<String, Variable> expected = new TreeMap<String, Variable>();
        for (Variable v : expectedVariables)
            expected.put(v.getName(), v);

        Assert.assertTrue("Wrong variable number", results.size() == expected.size());

        for (Variable variable : results.values())
        {
            final Variable expectedVariable = expected.get(variable.getName());
            Assert.assertTrue(
                String.format("Unexpected variable name. '%s'",
                    variable.getName()),
                    expectedVariable != null
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
    }

    private static void checkErrors(Iterable<String> errors)
    {
        final Iterator<String> errorIterator = errors.iterator();

        if (!errorIterator.hasNext())
            return;

        final StringBuilder errorStringBuilder = new StringBuilder();
        errorStringBuilder.append("Errors occured:");

        while (errorIterator.hasNext())
        {
            errorStringBuilder.append("\r\n");
            errorStringBuilder.append(errorIterator.next());
        }

        Assert.fail(errorStringBuilder.toString());
    }
}
