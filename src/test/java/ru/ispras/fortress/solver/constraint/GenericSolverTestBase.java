/*
 * Copyright (c) 2011 ISPRAS (www.ispras.ru)
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * GenericSolverTestBase.java, Dec 20, 2011 12:19:23 PM Andrei Tatarnikov
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

package ru.ispras.fortress.solver.constraint;

import java.io.File;
import java.io.IOException;

import org.junit.Assert;
import org.junit.Test;

import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.solver.Environment;
import ru.ispras.fortress.solver.Solver;
import ru.ispras.fortress.solver.SolverResult;
import ru.ispras.fortress.solver.SolverResultChecker;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.xml.XMLConstraintLoader;
import ru.ispras.fortress.solver.xml.XMLConstraintSaver;
import ru.ispras.fortress.solver.xml.XMLNotLoadedException;
import ru.ispras.fortress.solver.xml.XMLNotSavedException;

public abstract class GenericSolverTestBase
{
    public static interface SampleConstraint
    {
        public Constraint getConstraint();
        public Iterable<Variable> getExpectedVariables();
    }

    private final SampleConstraint sample;

    public GenericSolverTestBase(SampleConstraint sample)
    {
        if (null == sample)
            throw new NullPointerException();

        this.sample = sample;
    }

    @Test
    public final void runSolverTests()
    {
        final Constraint constraint = sample.getConstraint();
        solveAndCheckResult(constraint);
    }

    @Test
    public final void runSerializerTests()
    {
        final Constraint constraint = sample.getConstraint();
        final XMLConstraintSaver saver = new XMLConstraintSaver(constraint);

        File tempFile = null;

        try
        {
            // Saving to and loading from file. 
            tempFile = File.createTempFile(constraint.getName(), ".xml");

            final String tempFileName = tempFile.getPath();
            saver.saveToFile(tempFileName);

            final Constraint tempFileConstraint = XMLConstraintLoader.loadFromFile(tempFileName);
            ConstraintEqualityChecker.check(constraint, tempFileConstraint);

            solveAndCheckResult(tempFileConstraint);

            // Saving to and loading from string.
            final String xmlText = saver.saveToString();

            final Constraint xmlTextConstraint = XMLConstraintLoader.loadFromString(xmlText);
            ConstraintEqualityChecker.check(constraint, xmlTextConstraint);

            solveAndCheckResult(xmlTextConstraint);
        }
        catch (IOException e)
        {
            Assert.fail("Failed to create a temporary file for constraint " + constraint.getName() + ".");
        }
        catch (XMLNotSavedException e)
        {
            e.printStackTrace();
            Assert.fail(e.getMessage());
        }
        catch (XMLNotLoadedException e)
        {
            e.printStackTrace();
            Assert.fail(e.getMessage());
        }
        finally 
        {
            if (null != tempFile && !Environment.isDebugMode())
                tempFile.delete();
        }
    }

    private void solveAndCheckResult(Constraint constraint)
    {
        final Solver solver = constraint.getKind().getDefaultSolverId().getSolver();
        final SolverResult solverResult = solver.solve(constraint);

        SolverResultChecker.check(solverResult, sample.getExpectedVariables());
    }
}
