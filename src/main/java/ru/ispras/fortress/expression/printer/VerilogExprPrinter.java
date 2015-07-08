/*
 * Copyright 2014-2015 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.expression.printer;

import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.expression.printer.OperationDescription.Type;

/**
 * This class implements a Verilog-style expression printer.
 * 
 * @author <a href="mailto:kamkin@ispras.ru">Alexander Kamkin</a>
 */

final class VerilogExprPrinter extends MapBasedPrinter {
  public VerilogExprPrinter() {
    // Supported operations.
    addMapping(StandardOperation.MINUS, "-", Type.PREFIX);
    addMapping(StandardOperation.PLUS, "+", Type.PREFIX);
    addMapping(StandardOperation.NOT, "!", Type.PREFIX);
    addMapping(StandardOperation.BVNOT, "~", Type.PREFIX);
    addMapping(StandardOperation.BVANDR, "&", Type.PREFIX);
    addMapping(StandardOperation.BVNANDR, "~&", Type.PREFIX);
    addMapping(StandardOperation.BVORR, "|", Type.PREFIX);
    addMapping(StandardOperation.BVNORR, "~|", Type.PREFIX);
    addMapping(StandardOperation.BVXORR, "^", Type.PREFIX);
    addMapping(StandardOperation.BVXNORR, "~^", Type.PREFIX);
    addMapping(StandardOperation.POWER, "**", Type.INFIX);
    addMapping(StandardOperation.MUL, "*", Type.INFIX);
    addMapping(StandardOperation.BVMUL, "*", Type.INFIX); // BVMUL = MUL
    addMapping(StandardOperation.DIV, "/", Type.INFIX);
    addMapping(StandardOperation.MOD, "%", Type.INFIX);
    addMapping(StandardOperation.BVSMOD, "%", Type.INFIX); // BVSMOD = MOD
    addMapping(StandardOperation.ADD, "+", Type.INFIX);
    addMapping(StandardOperation.BVADD, "+", Type.INFIX); // BVADD = ADD
    addMapping(StandardOperation.SUB, "-", Type.INFIX);
    addMapping(StandardOperation.BVSUB, "-", Type.INFIX); // BVSUB = SUB
    addMapping(StandardOperation.BVLSHR, ">>", Type.INFIX);
    addMapping(StandardOperation.BVLSHL, "<<", Type.INFIX);
    addMapping(StandardOperation.BVASHR, ">>>", Type.INFIX);
    addMapping(StandardOperation.BVASHL, "<<<", Type.INFIX);
    addMapping(StandardOperation.LESS, "<", Type.INFIX);
    addMapping(StandardOperation.BVULT, "<", Type.INFIX); // BVULT = LESS
    addMapping(StandardOperation.BVSLT, "<", Type.INFIX); // BVSLT = LESS
    addMapping(StandardOperation.LESSEQ, "<=", Type.INFIX);
    addMapping(StandardOperation.BVULE, "<=", Type.INFIX); // BVULE = LESSEQ
    addMapping(StandardOperation.BVSLE, "<=", Type.INFIX); // BVSLE = LESSEQ
    addMapping(StandardOperation.GREATER, ">", Type.INFIX);
    addMapping(StandardOperation.BVUGT, ">", Type.INFIX); // BVUGT = GREATER
    addMapping(StandardOperation.BVSGT, ">", Type.INFIX); // BVSGT = GREATER
    addMapping(StandardOperation.GREATEREQ, ">=", Type.INFIX);
    addMapping(StandardOperation.BVUGE, ">=", Type.INFIX); // BVUGE = GREATEREQ
    addMapping(StandardOperation.BVSGE, ">=", Type.INFIX); // BVSGE = GREATEREQ
    addMapping(StandardOperation.EQ, "==", Type.INFIX);
    addMapping(StandardOperation.NOTEQ, "!=", Type.INFIX);
    addMapping(StandardOperation.EQCASE, "===", Type.INFIX);
    addMapping(StandardOperation.NOTEQCASE, "!==", Type.INFIX);
    addMapping(StandardOperation.BVAND, "&", Type.INFIX);
    addMapping(StandardOperation.BVNAND, "~&", Type.INFIX);
    addMapping(StandardOperation.BVXOR, "^", Type.INFIX);
    addMapping(StandardOperation.BVXNOR, "~^", Type.INFIX);
    addMapping(StandardOperation.BVOR, "|", Type.INFIX);
    addMapping(StandardOperation.BVNOR, "~|", Type.INFIX);
    addMapping(StandardOperation.AND, "&&", Type.INFIX);
    addMapping(StandardOperation.OR, "||", Type.INFIX);
    addMapping(StandardOperation.BVCONCAT, "{", ", ", "}");
    addMapping(StandardOperation.BVREPEAT, "{", "{", "}}");
    addMapping(StandardOperation.ITE, new String[] {"?", ":"});
    addMapping(StandardOperation.BVEXTRACT, "", new String[] {"[", ":"}, "]", new int[] {2, 0, 1});

    // Unsupported operations.
    addMapping(StandardOperation.BVROL, "BVROL(", ", ", ")");
    addMapping(StandardOperation.BVROR, "BVROR(", ", ", ")");
    addMapping(StandardOperation.BVUREM, "BVUREM(", ", ", ")");
    addMapping(StandardOperation.BVSREM, "BVSREM(", ", ", ")");
    addMapping(StandardOperation.BVZEROEXT, "BVZEROEXT(", ", ", ")");
    addMapping(StandardOperation.BVSIGNEXT, "BVSIGNEXT(", ", ", ")");
    addMapping(StandardOperation.REM, "REM(", ", ", ")");
    addMapping(StandardOperation.ABS, "ABS(", ", ", ")");
    addMapping(StandardOperation.MIN, "MIN(", ", ", ")");
    addMapping(StandardOperation.MAX, "MAX(", ", ", ")");
    addMapping(StandardOperation.IMPL, "IMPL(", ", ", ")");
    addMapping(StandardOperation.SELECT, "SELECT(", ", ", ")");
    addMapping(StandardOperation.STORE, "STORE(", ", ", ")");
  }
}
