/*
 * Copyright (c) 2014 ISPRAS (www.ispras.ru)
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * VerilogStylePrinter.java, Sep 9, 2014 13:47:21 PM Alexander Kamkin
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

import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.expression.printer.OperationDescription.Type;

/**
 * This class implements a Verilog-style expression printer.
 * 
 * @author <a href="mailto:kamkin@ispras.ru">Alexander Kamkin</a>
 */

final class VerilogExprPrinter extends MapBasedPrinter
{
    /**
     * Constructs a Verilog-style expression printer.
     */

    public VerilogExprPrinter()
    {
        addMapping(StandardOperation.MINUS,     "-",     Type.PREFIX);
        addMapping(StandardOperation.PLUS,      "+",     Type.PREFIX);
        addMapping(StandardOperation.NOT,       "!",     Type.PREFIX);
        addMapping(StandardOperation.BVNOT,     "~",     Type.PREFIX);
        addMapping(StandardOperation.BVANDR,    "&",     Type.PREFIX);
        addMapping(StandardOperation.BVNANDR,   "~&",    Type.PREFIX);
        addMapping(StandardOperation.BVORR,     "|",     Type.PREFIX);
        addMapping(StandardOperation.BVNORR,    "~|",    Type.PREFIX);
        addMapping(StandardOperation.BVXORR,    "^",     Type.PREFIX);
        addMapping(StandardOperation.BVXNORR,   "~^",    Type.PREFIX);
        addMapping(StandardOperation.POWER,     "**",    Type.INFIX);
        addMapping(StandardOperation.MUL,       "*",     Type.INFIX);
        addMapping(StandardOperation.DIV,       "/",     Type.INFIX);
        addMapping(StandardOperation.MOD,       "%",     Type.INFIX);
        addMapping(StandardOperation.ADD,       "+",     Type.INFIX);
        addMapping(StandardOperation.SUB,       "-",     Type.INFIX);
        addMapping(StandardOperation.BVLSHR,    ">>",    Type.INFIX);
        addMapping(StandardOperation.BVLSHL,    "<<",    Type.INFIX);
        addMapping(StandardOperation.BVASHR,    ">>>",   Type.INFIX);
        addMapping(StandardOperation.BVASHL,    "<<<",   Type.INFIX);
        addMapping(StandardOperation.LESS,      "<",     Type.INFIX);
        addMapping(StandardOperation.LESSEQ,    "<=",    Type.INFIX);
        addMapping(StandardOperation.GREATER,   ">",     Type.INFIX);
        addMapping(StandardOperation.GREATEREQ, ">=",    Type.INFIX);
        addMapping(StandardOperation.EQ,        "==",    Type.INFIX);
        addMapping(StandardOperation.NOTEQ,     "!=",    Type.INFIX);
        addMapping(StandardOperation.EQCASE,    "===",   Type.INFIX);
        addMapping(StandardOperation.NOTEQCASE, "!==",   Type.INFIX);
        addMapping(StandardOperation.BVAND,     "&",     Type.INFIX);
        addMapping(StandardOperation.BVNAND,    "~&",    Type.INFIX);
        addMapping(StandardOperation.BVXOR,     "^",     Type.INFIX);
        addMapping(StandardOperation.BVXNOR,    "~^",    Type.INFIX);
        addMapping(StandardOperation.BVOR,      "|",     Type.INFIX);
        addMapping(StandardOperation.BVNOR,     "~|",    Type.INFIX);
        addMapping(StandardOperation.AND,       "&&",    Type.INFIX);
        addMapping(StandardOperation.OR,        "||",    Type.INFIX);
        addMapping(StandardOperation.BVCONCAT,  "{", ", ", "}");
        addMapping(StandardOperation.BVREPEAT,  "{", "{", "}}");
        addMapping(StandardOperation.ITE,       new String[] { "?", ":" });

        // Unsupported in Verilog.
        addMapping(StandardOperation.BVROL,     "BVROL", Type.INFIX);
        addMapping(StandardOperation.BVROR,     "BVROR", Type.INFIX);
        addMapping(StandardOperation.MIN,       "MIN(", ", ", ")");
        addMapping(StandardOperation.MAX,       "MAX(", ", ", ")");
    }
}
