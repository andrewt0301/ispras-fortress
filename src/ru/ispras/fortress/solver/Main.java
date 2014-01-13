package ru.ispras.fortress.solver;

import java.io.File;
import java.io.IOException;

import org.junit.Assert;

import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.tests.samples.SimpleBitVector;
import ru.ispras.fortress.solver.xml.XMLConstraintSaver;
import ru.ispras.fortress.solver.xml.XMLNotSavedException;

public class Main
{
    /**
     * @param args main arguments
     */

    public static void main(String[] args)
    {
        System.out.println(System.getProperty("os.name"));
        System.out.println(System.getProperty("user.dir"));

        final Constraint constraint = new SimpleBitVector().getConstraint();
        String tempFile = null;

        try
        {
            tempFile = File.createTempFile(constraint.getName(), ".xml").getPath();
            final XMLConstraintSaver saver = new XMLConstraintSaver(tempFile, constraint);
            saver.save();
        }
        catch (IOException e)
        {
            Assert.fail("Failed to create a temporary file for constraint " + constraint.getName() + ".");
            e.printStackTrace();
        }
        catch (XMLNotSavedException e)
        {
            Assert.fail(e.getMessage());
            e.printStackTrace();
        }

        System.out.println("done");
    }
}
