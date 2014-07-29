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

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.net.URL;

import javax.xml.parsers.ParserConfigurationException;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;

import org.xml.sax.InputSource;
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
    private XMLConstraintLoader() {}
   
    /**
     * Loads a constraint from the specified XML file.
     *
     * @param fileName The full name of an XML file storing the constraint.
     * @return A constraint object loaded from the file.
     * 
     * @throws NullPointerException if the parameter equals null.
     * @throws XMLNotLoadedException if an issue occurred during parsing the XML document.
     */

    public static Constraint loadFromFile(String fileName) throws XMLNotLoadedException
    {
        if (null == fileName)
            throw new NullPointerException();

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

    /**
     * Creates a constraint from the specified XML string.
     *
     * @param text XML text describing a constraint.
     * @return A constraint object created from the XML text.
     * 
     * @throws NullPointerException if the parameter equals null.
     * @throws XMLNotLoadedException if an issue occurred during parsing the XML text.
     */

    public static Constraint loadFromString(String text) throws XMLNotLoadedException
    {
        if (null == text)
            throw new NullPointerException();

        try
        {
            final InputStream stream = 
                new ByteArrayInputStream(text.getBytes("UTF-8")); 

            final XMLConstraintHandler handler = new XMLConstraintHandler();
            newSAXParser().parse(stream, handler);

            return handler.getConstraint();
        }
        catch (Exception e)
        {
            throw new XMLNotLoadedException(e);
        }
    }

    /**
     * Loads a constraint from an XML file pointed by the specified URL.
     *
     * @param url URL that points to an XML file storing the constraint.
     * @return A constraint object loaded from the file.
     * 
     * @throws NullPointerException if the parameter equals null.
     * @throws XMLNotLoadedException if an issue occurred during parsing the XML document.
     */

    public static Constraint loadFromURL(URL url) throws XMLNotLoadedException
    {
        if (null == url)
            throw new NullPointerException();

        try
        {
            final XMLConstraintHandler handler = new XMLConstraintHandler();
            newSAXParser().parse(new InputSource(url.openStream()), handler);

            return handler.getConstraint();
        }
        catch (Exception e)
        {
            throw new XMLNotLoadedException(url.toString(), e);
        }
    }

    private static SAXParser newSAXParser() throws ParserConfigurationException, SAXException
    {
        final SAXParserFactory factory = SAXParserFactory.newInstance();
        return factory.newSAXParser();
    }
}
