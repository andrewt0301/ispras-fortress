/*
 * Copyright (c) 2012 ISPRAS
 *
 * Institute for System Programming of Russian Academy of Sciences
 *
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 *
 * All rights reserved.
 *
 * XMLConstraintLoader.java, Feb 1, 2012 12:22:42 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver.xml;

import javax.xml.parsers.ParserConfigurationException;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;
import org.xml.sax.SAXException;
import ru.ispras.fortress.solver.constraint.Constraint;

/**
 * The XMLConstraintLoader class provides functionality that loads a constraint
 * from the specified XML file.
 *
 * @author Andrei Tatarnikov
 */

public final class XMLConstraintLoader
{
    private final String fileName;

    /**
     * Constructs an XMLConstraintLoader object that will load 
     * a constraint from the specified XML document.
     * 
     * @param fileName XML document file name.
     * 
     * @throws NullPointerException if the parameter equals null.
     */

    public XMLConstraintLoader(String fileName)
    {
        if (null == fileName)
            throw new NullPointerException();

        this.fileName = fileName;
    }
   
    /**
     * Loads a constraint from the specified XML file.
     *
     * @param fileName The full name of the target path.
     * @return A constraint object loaded from the file.
     */

    public Constraint load() throws XMLNotLoadedException
    {
        try
        {
            final XMLConstraintHandler handler = new XMLConstraintHandler();
            newSAXParser().parse(fileName, handler);

            return handler.getConstraint();
        }
        catch (Exception e)
        {
            throw new XMLNotLoadedException(fileName, e);
        }
    }

    private static SAXParser newSAXParser() throws ParserConfigurationException, SAXException
    {
        final SAXParserFactory factory = SAXParserFactory.newInstance();
        return factory.newSAXParser();
    }
}
