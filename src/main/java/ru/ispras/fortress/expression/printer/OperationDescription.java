/*
 * Copyright (c) 2014 ISPRAS (www.ispras.ru)
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * VerilogStylePrinter.java, Sep 11, 2014 06:54:41 PM Alexander Kamkin
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

package ru.ispras.fortress.expression.printer;

/**
 * This class contains information on operation mapping.
 * 
 * @author <a href="mailto:kamkin@ispras.ru">Alexander Kamkin</a>
 */

final class OperationDescription
{
    /**
     * This enumeration contains the operation types.
     */
    public enum Type
    {
        /** The prefix operation. */
        PREFIX,
        /** The infix operation. */
        INFIX,
        /** The suffix operation. */
        SUFFIX
    }

    /** The operation prefix (string written before the first operand). */
    private String prefix;

    /** The operation infix(es) (string(s) written between two operands). */
    private String[] infix;

    /** The operation suffix (string written after the last operand). */
    private String suffix;

    /**
     * Constructs an operation description.
     * 
     * @param prefix the operation prefix.
     * @param infix the operation infixes.
     * @param suffix the operation suffix.
     */

    public OperationDescription(final String prefix, final String[] infix, final String suffix)
    {
        this.prefix = prefix;
        this.infix  = infix;
        this.suffix = suffix;
    }

    /**
     * Constructs an operation description.
     * 
     * @param prefix the operation prefix.
     * @param infix the operation infix.
     * @param suffix the operation suffix.
     */

    public OperationDescription(final String prefix, final String infix, final String suffix)
    {
        this(prefix, new String[] { infix }, suffix);
    }

    /**
     * Constructs an operation description.
     * 
     * @param sign the operation sign.
     * @param type the operation type.
     * @param addSpaces the flag indicating whether spaces before and after the operation sign are
     *                  required.
     */

    public OperationDescription(final String sign, final Type type, boolean addSpaces)
    {
        final String modifiedSign = addSpaces ? String.format(" %s ", sign) : sign;

        switch (type)
        {
        case PREFIX:
            prefix     = modifiedSign;
            break;
        case INFIX:
            prefix    = "(";
            infix     = new String[] { modifiedSign };
            suffix    = ")";
            break;
        case SUFFIX:
            suffix     = sign;
        }
    }

    /**
     * Constructs an operation description.
     * 
     * @param sign the operation sign.
     * @param type the operation type.
     */

    public OperationDescription(final String sign, final Type type)
    {
        this(sign, type, true);
    }

    /**
     * Constructs an operation description.
     * 
     * @param sign the operation signs.
     * @param addSpaces the flag indicating whether spaces before and after the operation sign are
     *                  required.
     */

    public OperationDescription(final String[] sign, boolean addSpaces)
    {
        final String[] modifiedSign = new String[sign.length];

        for (int i = 0; i < sign.length; i++)
            modifiedSign[i] = addSpaces ? String.format(" %s ", sign[i]) : sign[i];

        prefix    = "(";
        infix     = modifiedSign;
        suffix    = ")";
    }

    /**
     * Constructs an operation description.
     * 
     * @param sign the operation signs.
     */

    public OperationDescription(final String[] sign)
    {
        this(sign, true);
    }

    /**
     * Returns the operation prefix (string written before the first operand).
     * 
     * @return the operation prefix.
     */

    public String getPrefix()
    {
        return prefix;
    }

    /**
     * Returns the operation infix (string written between two operands).
     * 
     * @return the operation infix.
     */

    public String getInfix()
    {
        return infix[0];
    }

    /**
     * Returns the <code>i</code>-th operation infix (string written between <code>i</code>-th and
     * <code>(i+1)</code>-th operands).
     * 
     * @return the <code>i</code>-th operation infix.
     */

    public String getInfix(int i)
    {
        return infix[i];
    }

    /**
     * Returns the operation suffix (string written after the last operand). 
     * 
     * @return the operation suffix.
     */

    public String getSuffix()
    {
        return suffix;
    }
}
