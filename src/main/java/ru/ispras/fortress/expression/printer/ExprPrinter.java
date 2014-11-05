/*
 * Copyright (c) 2014 ISPRAS (www.ispras.ru)
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * ExprTreePrinterId.java, Sep 9, 2014 14:16:29 PM Alexander Kamkin
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

import ru.ispras.fortress.expression.Node;

/**
 * This enumeration contains identifiers of particular expression tree printers.
 *
 * @author <a href="mailto:kamkin@ispras.ru">Alexander Kamkin</a>
 */

public enum ExprPrinter implements ExprTreePrinter
{
    /** The VHDL-style expression tree printer. */

    VHDL(new VhdlExprPrinter()),

    /** The Verilog-style expression tree printer. */

    VERILOG(new VerilogExprPrinter());

    /** The implementation of the expression tree printer. */

    private ExprTreePrinter printer;

    private ExprPrinter(final ExprTreePrinter printer)
    {
        if (printer == null)
            throw new NullPointerException();

        this.printer = printer;
    }

    /**
     * Returns an array of expression tree printer names.
     *
     * @return printer names
     */
    public static String[] names() {
        ExprPrinter[] printers = ExprPrinter.values();
        String[] names = new String[printers.length];

        for (int i = 0; i < printers.length; i++) {
            names[i] = printers[i].name();
        }
        return names;
    }

    /**
    * Returns expression printer with the specified name.
     *
    * @param name printer name
    * @return {@link ru.ispras.fortress.expression.printer.ExprTreePrinter}
     * expression printer object or <code>null</code> if there is no printer
     * with such name
    */
    public static ExprTreePrinter getExprPrinter(String name) {

        ExprPrinter[] values = ExprPrinter.values();

        for (ExprPrinter value : values) {
            if (value.name().equalsIgnoreCase(name)) {
                return value;
            }
        }
        return null;
    }

    @Override
    public String toString(final Node node)
    {
        return printer.toString(node);
    }
}