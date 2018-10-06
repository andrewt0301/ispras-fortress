/*
 * Copyright 2017-2018 ISP RAS (http://www.ispras.ru)
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

import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeBinding;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.StandardOperation;

/**
 * This class implements an expression printer that produces SMT code.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public class SmtExprPrinter extends MapBasedPrinter {
  public SmtExprPrinter() {
    setVisitor(new Visitor());

     /* Logic Operations */
    addMapping(StandardOperation.EQ, SmtKeyword.EQ);
    addMapping(StandardOperation.NOTEQ, SmtKeyword.NOTEQ);
    addMapping(StandardOperation.EQCASE, SmtKeyword.EQCASE);
    addMapping(StandardOperation.NOTEQCASE, SmtKeyword.NOTEQCASE);
    addMapping(StandardOperation.AND, SmtKeyword.AND);
    addMapping(StandardOperation.OR, SmtKeyword.OR);
    addMapping(StandardOperation.NOT, SmtKeyword.NOT);
    addMapping(StandardOperation.XOR, SmtKeyword.XOR);
    addMapping(StandardOperation.IMPL, SmtKeyword.IMPL);
    addMapping(StandardOperation.ITE, SmtKeyword.IMPL);

    // Logic arithmetic
    addMapping(StandardOperation.MINUS, SmtKeyword.MINUS);
    addMapping(StandardOperation.PLUS, SmtKeyword.PLUS);
    addMapping(StandardOperation.ADD, SmtKeyword.ADD);
    addMapping(StandardOperation.SUB, SmtKeyword.SUB);
    addMapping(StandardOperation.MUL, SmtKeyword.MUL);
    addMapping(StandardOperation.DIV, SmtKeyword.DIV);
    addMapping(StandardOperation.MOD, SmtKeyword.MOD);
    addMapping(StandardOperation.GREATER, SmtKeyword.GREATER);
    addMapping(StandardOperation.GREATEREQ, SmtKeyword.GREATEREQ);
    addMapping(StandardOperation.LESS, SmtKeyword.LESS);
    addMapping(StandardOperation.LESSEQ, SmtKeyword.LESSEQ);
    addMapping(StandardOperation.POWER, SmtKeyword.POWER);

    // Basic Bitvector Arithmetic
    addMapping(StandardOperation.BVADD, SmtKeyword.BVADD);
    addMapping(StandardOperation.BVSUB, SmtKeyword.BVSUB);
    addMapping(StandardOperation.BVNEG, SmtKeyword.BVNEG);
    addMapping(StandardOperation.BVMUL, SmtKeyword.BVMUL);
    addMapping(StandardOperation.BVUDIV, SmtKeyword.BVUDIV);
    addMapping(StandardOperation.BVSDIV, SmtKeyword.BVSDIV);
    addMapping(StandardOperation.BVUREM, SmtKeyword.BVUREM);
    addMapping(StandardOperation.BVSREM, SmtKeyword.BVSREM);
    addMapping(StandardOperation.BVSMOD, SmtKeyword.BVSMOD);
    addMapping(StandardOperation.BVLSHL, SmtKeyword.BVLSHL);
    addMapping(StandardOperation.BVASHL, SmtKeyword.BVASHL);
    addMapping(StandardOperation.BVLSHR, SmtKeyword.BVLSHR);
    addMapping(StandardOperation.BVASHR, SmtKeyword.BVASHR);
    addMapping(StandardOperation.INT2BV, SmtKeyword.INT2BV);
    addMapping(StandardOperation.BVCONCAT, SmtKeyword.BVCONCAT);
    addMapping(StandardOperation.BVREPEAT, SmtKeyword.BVREPEAT);
    addMapping(StandardOperation.BVEXTRACT, SmtKeyword.BVEXTRACT);
    addMapping(StandardOperation.BVROL, SmtKeyword.BVROL);
    addMapping(StandardOperation.BVROR, SmtKeyword.BVROR);
    addMapping(StandardOperation.BVZEROEXT, SmtKeyword.BVZEROEXT);
    addMapping(StandardOperation.BVSIGNEXT, SmtKeyword.BVSIGNEXT);

    // Bitwise Operations
    addMapping(StandardOperation.BVOR, SmtKeyword.BVOR);
    addMapping(StandardOperation.BVXOR, SmtKeyword.BVXOR);
    addMapping(StandardOperation.BVAND, SmtKeyword.BVAND);
    addMapping(StandardOperation.BVNOT, SmtKeyword.BVNOT);
    addMapping(StandardOperation.BVNAND, SmtKeyword.BVNAND);
    addMapping(StandardOperation.BVNOR, SmtKeyword.BVNOR);
    addMapping(StandardOperation.BVXNOR, SmtKeyword.BVXNOR);

    // Predicates over Bitvectors
    addMapping(StandardOperation.BVULE, SmtKeyword.BVULE);
    addMapping(StandardOperation.BVULT, SmtKeyword.BVULT);
    addMapping(StandardOperation.BVUGE, SmtKeyword.BVUGE);
    addMapping(StandardOperation.BVUGT, SmtKeyword.BVUGT);
    addMapping(StandardOperation.BVSLE, SmtKeyword.BVSLE);
    addMapping(StandardOperation.BVSLT, SmtKeyword.BVSLT);
    addMapping(StandardOperation.BVSGE, SmtKeyword.BVSGE);
    addMapping(StandardOperation.BVSGT, SmtKeyword.BVSGT);

    /* Array operations */
    addMapping(StandardOperation.SELECT, SmtKeyword.SELECT);
    addMapping(StandardOperation.STORE, SmtKeyword.STORE);
  }

  protected final void addMapping(final StandardOperation op, final SmtKeyword id) {
    addMapping(op, id.getName());
  }

  protected final void addMapping(final StandardOperation op, final String sign) {
    addMapping(op, sign + " ", " ", "");
  }

  protected class Visitor extends ExprTreeVisitor {
    @Override
    public void onVariable(final NodeVariable variable) {
      if (variable.getData().hasValue()) {
        onValue(new NodeValue(variable.getData()));
      } else {
        super.onVariable(variable);
      }
    }

    @Override
    public void onOperationBegin(final NodeOperation expr) {
      appendText("(");
      if (StandardOperation.isParametric(expr.getOperationId())) {
        appendText("_ ");
      }

      super.onOperationBegin(expr);
    }

    @Override
    public void onOperationEnd(final NodeOperation expr) {
      appendText(")");
    }

    @Override
    public void onOperandEnd(
        final NodeOperation expr,
        final Node node,
        final int index) {
      final Enum<?> op = expr.getOperationId();
      if (StandardOperation.isParametric(op)
          && StandardOperation.getParameterCount(op) - 1 == index) {
        appendText(")");
      }
    }

    @Override
    public void onBindingBegin(final NodeBinding node) {
      appendText("(let (");
    }

    @Override
    public void onBindingListEnd(final NodeBinding node) {
      appendText(")");
    }

    @Override
    public void onBindingEnd(final NodeBinding node) {
      appendText(")");
    }

    @Override
    public void onBoundVariableBegin(
        final NodeBinding node,
        final NodeVariable variable,
        final Node value) {
      appendText("(");
      appendText(variable.getName());
      appendText(" ");
    }

    @Override
    public void onBoundVariableEnd(
        final NodeBinding node,
        final NodeVariable variable,
        final Node value) {
      appendText(")");
    }
  }
}
