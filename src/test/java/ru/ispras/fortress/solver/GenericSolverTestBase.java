/*
 * Copyright (c) 2011 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * SolverTestCases.java, Dec 20, 2011 12:19:23 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.TreeMap;

import org.junit.Assert;
import org.junit.BeforeClass;
import org.junit.Test;

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeExpr;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.solver.Environment;
import ru.ispras.fortress.solver.Solver;
import ru.ispras.fortress.solver.SolverId;
import ru.ispras.fortress.solver.SolverResult;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.Formulas;
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

            final Constraint loadedConstraint = XMLConstraintLoader.load(tempFile);
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

final class ConstraintEqualityChecker
{
	private ConstraintEqualityChecker() {}

    public static void check(Constraint expected, Constraint actual)
    {
        Assert.assertNotNull(expected);
        Assert.assertNotNull(actual);
        Assert.assertFalse("The same object", expected == actual);
        
        Assert.assertTrue("Constraint names do not match.", expected.getName().equals(actual.getName()));
        Assert.assertTrue("Constraint kinds.", expected.getKind() == actual.getKind());
        Assert.assertTrue("Constraint descriptions do not match.", expected.getDescription().equals(actual.getDescription()));
        
        check((Formulas)expected.getInnerRep(), (Formulas)actual.getInnerRep());
    }

    public static void check(Formulas expected, Formulas actual)
    {
        Assert.assertNotNull(expected);
        Assert.assertNotNull(actual);
        Assert.assertFalse("The same object", expected == actual);

        Assert.assertNotNull(expected.exprs());
        Assert.assertNotNull(actual.exprs());
        Assert.assertFalse("The same object", expected.exprs() == actual.exprs());

        final Iterator<Node> expectedIterator = expected.exprs().iterator();
        final Iterator<Node> actualIterator = actual.exprs().iterator();

        while (expectedIterator.hasNext() && actualIterator.hasNext())
            check(expectedIterator.next(), actualIterator.next());

        Assert.assertTrue("The numbers of formulas are different.", expectedIterator.hasNext() == actualIterator.hasNext());
    }

    public static void check(NodeExpr expected, NodeExpr actual)
    {
        Assert.assertNotNull(expected);
        Assert.assertNotNull(actual);
        Assert.assertFalse("The same object", expected == actual);

        Assert.assertTrue("Invalid element ID.", expected.getKind() == Node.Kind.EXPR);
        Assert.assertTrue("Invalid element ID.", actual.getKind() == Node.Kind.EXPR);
        Assert.assertTrue("Different operation IDs.", expected.getOperationId().equals(actual.getOperationId()));

        // TODO: Temporary requirement. Once the getDataType method is implemented to return a proper value
        // this code must be replaced with a proper check.
        // Assert.assertNull(expected.getDataType());
        // Assert.assertNull(actual.getDataType());

        int operandIndex = 0;
        while (operandIndex < expected.getOperandCount())
        {
            if ((null != expected.getOperand(operandIndex)) && 
                (null != actual.getOperand(operandIndex)))
            {
                check(expected.getOperand(operandIndex), actual.getOperand(operandIndex));
            }

            ++operandIndex;
        }
    }

    public static void check(NodeVariable expected, NodeVariable actual)
    {
        Assert.assertNotNull(expected);
        Assert.assertNotNull(actual);
        Assert.assertFalse("The same object", expected == actual);

        Assert.assertTrue("Invalid node kind.", expected.getKind() == Node.Kind.VARIABLE);
        Assert.assertTrue("Invalid node kind.", actual.getKind() == Node.Kind.VARIABLE);

        Assert.assertTrue("Variable names do not match.", expected.getName().equals(actual.getName()));

        check(expected.getData().getType(), actual.getData().getType());
        if (!
             ((null == expected.getValue()) && (null == actual.getValue()))
           )
        {
            Assert.assertTrue("Variable values do not match.", expected.getValue().equals(actual.getValue()));
        }
    }

    public static void check(NodeValue expected, NodeValue actual)
    {
        Assert.assertNotNull(expected);
        Assert.assertNotNull(actual);
        Assert.assertFalse("The same object", expected == actual);

        Assert.assertTrue("Invalid element ID.", expected.getKind() == Node.Kind.VALUE);
        Assert.assertTrue("Invalid element ID.", actual.getKind() == Node.Kind.VALUE);
        check(expected.getData().getType(), actual.getData().getType());
        Assert.assertTrue("Values do not match.", expected.getValue().equals(actual.getValue()));
    }

    public static void check(Node expected, Node actual)
    {
        Assert.assertNotNull(expected);
        Assert.assertNotNull(actual);

        Assert.assertFalse("The same object", expected == actual);
        Assert.assertTrue("Different element IDs.", expected.getKind() == actual.getKind());

        switch(expected.getKind())
        {
        case VALUE:
            check((NodeValue) expected, (NodeValue) actual);
            break;

        case VARIABLE:
            check((NodeVariable) expected, (NodeVariable) actual);
            break;

        case EXPR:
            check((NodeExpr) expected, (NodeExpr) actual);
            break;

        default:
            Assert.fail("Unknown element type.");
            break;
        }
    }

    public static void check(DataType expected, DataType actual)
    {
        Assert.assertNotNull(expected);
        Assert.assertNotNull(actual);

        Assert.assertTrue("Data type IDs do not match.", expected.getTypeId() == actual.getTypeId());
        Assert.assertTrue("Data type sizes do not match.", expected.getSize() == actual.getSize());
    }
}

final class SolverResultChecker
{   
	private SolverResultChecker() {}
	
    public static void check(SolverResult solverResult, Iterable<Variable> expectedVariables)
    {
        checkErrors(solverResult.getErrors());

        Assert.assertTrue("Failed to solve the constraint. Status: " +
           solverResult.getStatus(), solverResult.getStatus() == SolverResult.Status.SAT);

        final Iterator<Variable> expectedVariableIterator = expectedVariables.iterator();
        final Iterator<Variable> variableIterator = solverResult.getVariables().iterator();

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

