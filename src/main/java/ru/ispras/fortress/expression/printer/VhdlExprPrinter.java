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
        // Supported operations.
        addMapping(StandardOperation.MINUS,     "-",   Type.PREFIX);
        addMapping(StandardOperation.PLUS,      "+",   Type.PREFIX);
        addMapping(StandardOperation.NOT,       "NOT", Type.PREFIX);
        addMapping(StandardOperation.BVNOT,     "NOT", Type.PREFIX); // BVNOT = NOT
        addMapping(StandardOperation.POWER,     "**",  Type.INFIX);
        addMapping(StandardOperation.MUL,       "*",   Type.INFIX);
        addMapping(StandardOperation.BVMUL,     "*",   Type.INFIX); // BVMUL = MUL
        addMapping(StandardOperation.DIV,       "/",   Type.INFIX);
        addMapping(StandardOperation.MOD,       "MOD", Type.INFIX);
        addMapping(StandardOperation.BVSMOD,    "MOD", Type.INFIX); // BVSMOD = MOD
        addMapping(StandardOperation.ADD,       "+",   Type.INFIX);
        addMapping(StandardOperation.BVADD,     "+",   Type.INFIX); // BVADD = ADD
        addMapping(StandardOperation.SUB,       "-",   Type.INFIX);
        addMapping(StandardOperation.BVSUB,     "-",   Type.INFIX); // BVSUB = SUB
        addMapping(StandardOperation.BVLSHR,    "SRL", Type.INFIX);
        addMapping(StandardOperation.BVLSHL,    "SLL", Type.INFIX);
        addMapping(StandardOperation.BVASHR,    "SRA", Type.INFIX);
        addMapping(StandardOperation.BVASHL,    "SLA", Type.INFIX);
        addMapping(StandardOperation.BVROR,     "ROR", Type.INFIX);
        addMapping(StandardOperation.BVROL,     "ROL", Type.INFIX);
        addMapping(StandardOperation.LESS,      "<",   Type.INFIX);
        addMapping(StandardOperation.BVULT,     "<",   Type.INFIX); // BVULT = LESS
        addMapping(StandardOperation.BVSLT,     "<",   Type.INFIX); // BVSLT = LESS
        addMapping(StandardOperation.LESSEQ,    "<=",  Type.INFIX);
        addMapping(StandardOperation.BVULE,     "<=",  Type.INFIX); // BVULE = LESSEQ
        addMapping(StandardOperation.BVSLE,     "<=",  Type.INFIX); // BVSLE = LESSEQ
        addMapping(StandardOperation.GREATER,   ">",   Type.INFIX);
        addMapping(StandardOperation.BVUGT,     ">",   Type.INFIX); // BVUGT = GREATER
        addMapping(StandardOperation.BVSGT,     ">",   Type.INFIX); // BVSGT = GREATER
        addMapping(StandardOperation.GREATEREQ, ">=",  Type.INFIX);
        addMapping(StandardOperation.BVUGE,     ">=",  Type.INFIX); // BVUGE = GREATEREQ
        addMapping(StandardOperation.BVSGE,     ">=",  Type.INFIX); // BVSGE = GREATEREQ
        addMapping(StandardOperation.EQ,        "=",   Type.INFIX);
        addMapping(StandardOperation.NOTEQ,     "/=",  Type.INFIX);
        addMapping(StandardOperation.EQCASE,    "=",   Type.INFIX); // EQCASE = EQ
        addMapping(StandardOperation.NOTEQCASE, "/=",  Type.INFIX); // NOTEQCASE = NOTEQ
        addMapping(StandardOperation.AND,       "AND", Type.INFIX);
        addMapping(StandardOperation.BVAND,     "AND", Type.INFIX); // BVAND = AND
        addMapping(StandardOperation.OR,        "OR",  Type.INFIX);
        addMapping(StandardOperation.BVOR,      "OR",  Type.INFIX); // BVOR = OR
        addMapping(StandardOperation.BVXOR,     "XOR", Type.INFIX);
        addMapping(StandardOperation.BVNOR,     "NOR", Type.INFIX);
        addMapping(StandardOperation.BVCONCAT,  "&",   Type.INFIX);
        addMapping(StandardOperation.MIN,       "MINIMUM(", ", ", ")");
        addMapping(StandardOperation.MAX,       "MAXIMUM(", ", ", ")");
        addMapping(StandardOperation.ITE,       new String[] { "?", ":" });

        // Unsupported operations.
        addMapping(StandardOperation.BVNAND,    "BVNAND(", ", ", ")");
        addMapping(StandardOperation.BVXNOR,    "BVZNOR(", ", ", ")");
        addMapping(StandardOperation.BVANDR,    "BVANDR(", ", ", ")");
        addMapping(StandardOperation.BVNANDR,   "BVNANDR(", ", ", ")");
        addMapping(StandardOperation.BVORR,     "BVORR(", ", ", ")");
        addMapping(StandardOperation.BVNORR,    "BVNORR(", ", ", ")");
        addMapping(StandardOperation.BVXORR,    "BVXORR(", ", ", ")");
        addMapping(StandardOperation.BVXNORR,   "BVXNORR(", ", ", ")");
        addMapping(StandardOperation.BVREPEAT,  "BVREPEAT(", ", ", ")");
        addMapping(StandardOperation.BVEXTRACT, "BVEXTRACT(", ", ", ")");

        addMapping(StandardOperation.BVUREM,    "BVUREM(", ", ", ")");
        addMapping(StandardOperation.BVSREM,    "BVSREM(", ", ", ")");
        addMapping(StandardOperation.BVZEROEXT, "BVZEROEXT(", ", ", ")");
        addMapping(StandardOperation.BVSIGNEXT, "BVSIGNEXT(", ", ", ")");
        addMapping(StandardOperation.REM,       "REM(", ", ", ")");
        addMapping(StandardOperation.ABS,       "ABS(", ", ", ")");
        addMapping(StandardOperation.IMPL,      "IMPL(", ", ", ")");
        addMapping(StandardOperation.SELECT,    "SELECT(", ", ", ")");
        addMapping(StandardOperation.STORE,     "STORE(", ", ", ")");
    }
}
