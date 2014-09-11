/*
 * Copyright (c) 2014 ISPRAS (www.ispras.ru)
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * VhdlStylePrinter.java, Sep 9, 2014 13:47:21 PM Sergey Smolov
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
 * This class implements a VHDL-style expression printer.
 *
 * @author <a href="mailto:smolov@ispras.ru">Sergey Smolov</a>
 */

final class VhdlExprPrinter extends MapBasedPrinter
{
    /**
     * Constructs a VHDL-style expression printer.
     */

    public VhdlExprPrinter()
    {
        addMapping(StandardOperation.MINUS,     "-",   Type.PREFIX);
        addMapping(StandardOperation.PLUS,      "+",   Type.PREFIX);
        addMapping(StandardOperation.NOT,       "not", Type.PREFIX);
        addMapping(StandardOperation.BVNOT,     "not", Type.PREFIX);
        addMapping(StandardOperation.POWER,     "**",  Type.INFIX);
        addMapping(StandardOperation.MUL,       "*",   Type.INFIX);
        addMapping(StandardOperation.DIV,       "/",   Type.INFIX);
        addMapping(StandardOperation.MOD,       "mod", Type.INFIX);
        addMapping(StandardOperation.ADD,       "+",   Type.INFIX);
        addMapping(StandardOperation.SUB,       "-",   Type.INFIX);
        addMapping(StandardOperation.BVLSHR,    "srl", Type.INFIX);
        addMapping(StandardOperation.BVLSHL,    "sll", Type.INFIX);
        addMapping(StandardOperation.BVASHR,    "sra", Type.INFIX);
        addMapping(StandardOperation.BVASHL,    "sla", Type.INFIX);
        addMapping(StandardOperation.BVROL,     "rol", Type.INFIX);
        addMapping(StandardOperation.BVROR,     "ror", Type.INFIX);
        addMapping(StandardOperation.LESS,      "<",   Type.INFIX);
        addMapping(StandardOperation.LESSEQ,    "<=",  Type.INFIX);
        addMapping(StandardOperation.GREATER,   ">",   Type.INFIX);
        addMapping(StandardOperation.GREATEREQ, ">=",  Type.INFIX);
        addMapping(StandardOperation.EQ,        "=",   Type.INFIX);
        addMapping(StandardOperation.NOTEQ,     "/=",  Type.INFIX);
        addMapping(StandardOperation.EQCASE,    "=",   Type.INFIX);
        addMapping(StandardOperation.NOTEQCASE, "/=",  Type.INFIX);
        addMapping(StandardOperation.BVAND,     "and", Type.INFIX);
        addMapping(StandardOperation.BVXOR,     "xor", Type.INFIX);
        addMapping(StandardOperation.BVOR,      "or",  Type.INFIX);
        addMapping(StandardOperation.AND,       "and", Type.INFIX);
        addMapping(StandardOperation.OR,        "or",  Type.INFIX);
        addMapping(StandardOperation.BVCONCAT,  "&",   Type.INFIX);
        addMapping(StandardOperation.ITE,       new String[] { "?", ":" });
    }
}
