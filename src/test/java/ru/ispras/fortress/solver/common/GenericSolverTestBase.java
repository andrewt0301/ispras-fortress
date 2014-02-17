/*
 * Copyright (c) 2011 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * $Id: SolverTestCases.java, Dec 20, 2011 12:19:23 PM Andrei Tatarnikov Exp $
 */

package ru.ispras.fortress.solver.common;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;

import org.junit.Assert;
import org.junit.BeforeClass;
import org.junit.Test;

import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.solver.Environment;
import ru.ispras.fortress.solver.Solver;
import ru.ispras.fortress.solver.SolverId;
import ru.ispras.fortress.solver.SolverResult;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.xml.XMLConstraintLoader;
import ru.ispras.fortress.solver.xml.XMLConstraintSaver;
import ru.ispras.fortress.solver.xml.XMLNotLoadedException;
import ru.ispras.fortress.solver.xml.XMLNotSavedException;

public abstract class GenericSolverTestBase
{
    @BeforeClass
    public static void init()
    {
        if (Environment.isUnix())
        {
            Environment.setSolverPath("tools/z3/bin/z3");
        }
        else if(Environment.isWindows())
        {
            Environment.setSolverPath("tools/z3/bin/z3.exe");
        }
        else if (Environment.isOSX())
        {
        	Environment.setSolverPath("tools/z3/bin/z3");
        }
        else
        {
            // TODO: add initialization code for other platforms.
            fail("Unsupported platform. Please set up paths to the external engine. Platform name: " + 
                 System.getProperty("os.name"));
        }

        String solverPath = "";
        
        try {
            solverPath = new File(Environment.getSolverPath()).getCanonicalPath();
        } catch (IOException e) {
            e.printStackTrace();
        }

        assertTrue("The solver engine executable is not found. Path: " + solverPath, 
                new File(Environment.getSolverPath()).isFile());
    }

    @Test
    public void runSolverTests()
    {
        final Constraint constraint = getConstraint();
        
        final Solver solver = constraint.getKind().getDefaultSolverId().getSolver();
        final SolverResult solverResult = solver.solve(constraint);

        SolverResultChecker.check(solverResult, getExpectedVariables());
    }

    @Test
    public void runSerializerTests()
    {
        final Constraint constraint = getConstraint();

        try
        {
            final String tempFile = File.createTempFile(constraint.getName(), ".xml").getPath();

            final XMLConstraintSaver saver = new XMLConstraintSaver(tempFile, constraint);
            saver.save();

            final Constraint loadedConstraint = new XMLConstraintLoader(tempFile).load();
            ConstraintEqualityChecker.check(constraint, loadedConstraint);
            
            final Solver solver = constraint.getKind().getDefaultSolverId().getSolver();
            final SolverResult solverResult = solver.solve(loadedConstraint);

            SolverResultChecker.check(solverResult, getExpectedVariables());
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
    }

    public Iterable<SolverId> getSolvers()
    {
        ArrayList<SolverId> result = new ArrayList<SolverId>();

        result.add(SolverId.Z3_TEXT);
        result.add(SolverId.DEFAULT);

        return result;
    }

    public abstract Constraint getConstraint();
    public abstract Iterable<Variable> getExpectedVariables();
}
