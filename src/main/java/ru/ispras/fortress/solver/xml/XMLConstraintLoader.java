/*
 * Copyright 2012-2014 ISP RAS (http://www.ispras.ru)
 * 
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 * 
 * http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software distributed under the License
 * is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
 * or implied. See the License for the specific language governing permissions and limitations under
 * the License.
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
import ru.ispras.fortress.util.InvariantChecks;

/**
 * The XMLConstraintLoader class provides functionality that loads a constraint from the specified
 * XML file.
 * 
 * @author Andrei Tatarnikov
 */

public final class XMLConstraintLoader {
  private XMLConstraintLoader() {}

  /**
   * Loads a constraint from the specified XML file.
   * 
   * @param fileName The full name of an XML file storing the constraint.
   * @return A constraint object loaded from the file.
   * 
   * @throws IllegalArgumentException if the parameter equals null.
   * @throws XMLNotLoadedException if an issue occurred during parsing the XML document.
   */

  public static Constraint loadFromFile(final String fileName) throws XMLNotLoadedException {
    InvariantChecks.checkNotNull(fileName);

    try {
      final XMLConstraintHandler handler = new XMLConstraintHandler();
      newSAXParser().parse(fileName, handler);
      return handler.getConstraint();
    } catch (Exception e) {
      throw new XMLNotLoadedException(fileName, e);
    }
  }

  /**
   * Creates a constraint from the specified XML string.
   * 
   * @param text XML text describing a constraint.
   * @return A constraint object created from the XML text.
   * 
   * @throws IllegalArgumentException if the parameter equals null.
   * @throws XMLNotLoadedException if an issue occurred during parsing the XML text.
   */

  public static Constraint loadFromString(final String text) throws XMLNotLoadedException {
    InvariantChecks.checkNotNull(text);

    try {
      final InputStream stream = new ByteArrayInputStream(text.getBytes("UTF-8"));
      final XMLConstraintHandler handler = new XMLConstraintHandler();
      newSAXParser().parse(stream, handler);
      return handler.getConstraint();
    } catch (Exception e) {
      throw new XMLNotLoadedException(e);
    }
  }

  /**
   * Loads a constraint from an XML file pointed by the specified URL.
   * 
   * @param url URL that points to an XML file storing the constraint.
   * @return A constraint object loaded from the file.
   * 
   * @throws IllegalArgumentException if the parameter equals null.
   * @throws XMLNotLoadedException if an issue occurred during parsing the XML document.
   */

  public static Constraint loadFromURL(final URL url) throws XMLNotLoadedException {
    InvariantChecks.checkNotNull(url);

    try {
      final XMLConstraintHandler handler = new XMLConstraintHandler();
      newSAXParser().parse(new InputSource(url.openStream()), handler);
      return handler.getConstraint();
    } catch (Exception e) {
      throw new XMLNotLoadedException(url.toString(), e);
    }
  }

  private static SAXParser newSAXParser() throws ParserConfigurationException, SAXException {
    final SAXParserFactory factory = SAXParserFactory.newInstance();
    return factory.newSAXParser();
  }
}
