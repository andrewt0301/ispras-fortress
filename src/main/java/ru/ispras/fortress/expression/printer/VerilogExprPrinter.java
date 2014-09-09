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

import ru.ispras.fortress.expression.ExprTreeVisitorDefault;
import ru.ispras.fortress.expression.ExprTreeWalker;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.StandardOperation;

/**
 * This class implements a Verilog-style expression tree printer.
 * 
 * @author <a href="mailto:kamkin@ispras.ru">Alexander Kamkin</a>
 */

final class VerilogExprPrinter implements ExprTreePrinter
{
    final class ExprTreeVisitor extends ExprTreeVisitorDefault
    {
        private StringBuffer buffer = new StringBuffer();

        @Override
        public void onOperationBegin(final NodeOperation expr)
        {
            final Enum<?> op = expr.getOperationId();
            
            // Brackets are not required for primary expressions.
            if (op != StandardOperation.BVCONCAT
             && op != StandardOperation.BVREPEAT)
            {
                buffer.append("(");
            }
        }

        @Override
        public void onOperationEnd(final NodeOperation expr)
        {
            final Enum<?> op = expr.getOperationId();

            // Brackets are not required for primary expressions.
            if (op != StandardOperation.BVCONCAT
             && op != StandardOperation.BVREPEAT)
            {
                buffer.append(")");
            }
        }

        @Override
        public void onOperandBegin(final NodeOperation expr, final Node operand, int index)
        {
            final Enum<?> op = expr.getOperationId();

            // Unary operations and concatenations.
            if (index == 0)
            {
                if (op == StandardOperation.MINUS)
                {
                    buffer.append("-");
                }
                else if (op == StandardOperation.PLUS)
                {
                    buffer.append("+");
                }
                else if (op == StandardOperation.NOT)
                {
                    buffer.append("!");
                }
                else if (op == StandardOperation.BVNOT)
                {
                    buffer.append("~");
                }
                else if (op == StandardOperation.BVANDR)
                {
                    buffer.append("&");
                }
                else if (op == StandardOperation.BVNANDR)
                {
                    buffer.append("~&");
                }
                else if (op == StandardOperation.BVORR)
                {
                    buffer.append("|");
                }
                else if (op == StandardOperation.BVNORR)
                {
                    buffer.append("~|");
                }
                else if (op == StandardOperation.BVXORR)
                {
                    buffer.append("^");
                }
                else if (op == StandardOperation.BVXNORR)
                {
                    buffer.append("~^");
                }
                else if (op == StandardOperation.BVCONCAT)
                {
                    buffer.append("{");
                }
                else if (op == StandardOperation.BVREPEAT)
                {
                    buffer.append("{");
                }
            }
            // Binary and ternary operations.
            else if (index == 1)
            {
                final boolean space = (op != StandardOperation.BVCONCAT)
                                   && (op != StandardOperation.BVREPEAT);

                if (space)
                {
                    buffer.append(" ");
                }

                if (op == StandardOperation.POWER)
                {
                    buffer.append("**");
                }
                else if (op == StandardOperation.MUL)
                {
                    buffer.append("*");
                }
                else if (op == StandardOperation.DIV)
                {
                    buffer.append("/");
                }
                else if (op == StandardOperation.MOD)
                {
                    buffer.append("%");
                }
                else if (op == StandardOperation.ADD)
                {
                    buffer.append("+");
                }
                else if (op == StandardOperation.SUB)
                {
                    buffer.append("-");
                }
                else if (op == StandardOperation.BVLSHR)
                {
                    buffer.append(">>");
                }
                else if (op == StandardOperation.BVLSHL)
                {
                    buffer.append("<<");
                }
                else if (op == StandardOperation.BVASHR)
                {
                    buffer.append(">>>");
                }
                else if (op == StandardOperation.BVASHL)
                {
                    buffer.append("<<<");
                }
                else if (op == StandardOperation.LESS)
                {
                    buffer.append("<");
                }
                else if (op == StandardOperation.LESSEQ)
                {
                    buffer.append("<=");
                }
                else if (op == StandardOperation.GREATER)
                {
                    buffer.append(">");
                }
                else if (op == StandardOperation.GREATEREQ)
                {
                    buffer.append(">=");
                }
                else if (op == StandardOperation.EQ)
                {
                    buffer.append("==");
                }
                else if (op == StandardOperation.NOTEQ)
                {
                    buffer.append("!=");
                }
                else if (op == StandardOperation.EQCASE)
                {
                    buffer.append("===");
                }
                else if (op == StandardOperation.NOTEQCASE)
                {
                    buffer.append("!==");
                }
                else if (op == StandardOperation.BVAND)
                {
                    buffer.append("&");
                }
                else if (op == StandardOperation.BVNAND)
                {
                    buffer.append("~&");
                }
                else if (op == StandardOperation.BVXOR)
                {
                    buffer.append("^");
                }
                else if (op == StandardOperation.BVXNOR)
                {
                    buffer.append("~^");
                }
                else if (op == StandardOperation.BVOR)
                {
                    buffer.append("|");
                }
                else if (op == StandardOperation.BVNOR)
                {
                    buffer.append("~|");
                }
                else if (op == StandardOperation.AND)
                {
                    buffer.append("&&");
                }
                else if (op == StandardOperation.OR)
                {
                    buffer.append("||");
                }
                else if (op == StandardOperation.ITE)
                {
                    buffer.append("?");
                }
                else if (op == StandardOperation.BVCONCAT)
                {
                    buffer.append(", ");
                }
                else if (op == StandardOperation.BVREPEAT)
                {
                    buffer.append("{");
                }

                if (space)
                {
                    buffer.append(" ");
                }
            }
            // Ternary operations.
            else if (index == 2)
            {
                buffer.append(" ");
                {
                    if (op == StandardOperation.ITE)
                    {
                        buffer.append(":");
                    }
                }
                buffer.append(" ");
            }
        }

        @Override
        public void onOperandEnd(final NodeOperation expr, final Node operand, int index)
        {
            final Enum<?> op = expr.getOperationId();

            // Repeat and concatenation.
            if (index == 1)
            {
                if (op == StandardOperation.BVCONCAT)
                {
                    buffer.append("}");
                }
                else if (op == StandardOperation.BVREPEAT)
                {
                    buffer.append("}}");
                }
            }
        }

        @Override
        public void onValue(final NodeValue value)
        {
            buffer.append(value.toString());
        }

        @Override
        public void onVariable(final NodeVariable variable)
        {
            buffer.append(variable.getName());
        }

        /**
         * Returns the string representation of the expression tree.
         * 
         * @return the string representation of the expression tree.
         */

        public String toString()
        {
            return buffer.toString();
        }
    }

    @Override
    public String toString(final Node node)
    {
        final ExprTreeVisitor visitor = new ExprTreeVisitor();
        final ExprTreeWalker walker = new ExprTreeWalker(visitor);

        walker.visit(node);

        return visitor.toString();
    }
}
