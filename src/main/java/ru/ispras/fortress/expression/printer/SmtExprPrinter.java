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
    addMapping(StandardOperation.EQ, "=");
    addMapping(StandardOperation.NOTEQ, "distinct");
    addMapping(StandardOperation.EQCASE, "=");
    addMapping(StandardOperation.NOTEQCASE, "distinct");
    addMapping(StandardOperation.AND, "and");
    addMapping(StandardOperation.OR, "or");
    addMapping(StandardOperation.NOT, "not");
    addMapping(StandardOperation.XOR, "xor");
    addMapping(StandardOperation.IMPL, "=>");
    addMapping(StandardOperation.ITE, "ite");

    // Logic arithmetic
    addMapping(StandardOperation.MINUS, "-");
    addMapping(StandardOperation.PLUS, "+");
    addMapping(StandardOperation.ADD, "+");
    addMapping(StandardOperation.SUB, "-");
    addMapping(StandardOperation.MUL, "*");
    addMapping(StandardOperation.DIV, "div");
    addMapping(StandardOperation.MOD, "mod");
    addMapping(StandardOperation.GREATER, ">");
    addMapping(StandardOperation.GREATEREQ, ">=");
    addMapping(StandardOperation.LESS, "<");
    addMapping(StandardOperation.LESSEQ, "<=");
    addMapping(StandardOperation.POWER, "^");

    // Basic Bitvector Arithmetic
    addMapping(StandardOperation.BVADD, "bvadd");
    addMapping(StandardOperation.BVSUB, "bvsub");
    addMapping(StandardOperation.BVNEG, "bvneg");
    addMapping(StandardOperation.BVMUL, "bvmul");
    addMapping(StandardOperation.BVUDIV, "bvudiv");
    addMapping(StandardOperation.BVSDIV, "bvsdiv");
    addMapping(StandardOperation.BVUREM, "bvurem");
    addMapping(StandardOperation.BVSREM, "bvsrem");
    addMapping(StandardOperation.BVSMOD, "bvsmod");
    addMapping(StandardOperation.BVLSHL, "bvshl");
    addMapping(StandardOperation.BVASHL, "bvshl");
    addMapping(StandardOperation.BVLSHR, "bvlshr");
    addMapping(StandardOperation.BVASHR, "bvashr");
    addMapping(StandardOperation.INT2BV, "int2bv");
    addMapping(StandardOperation.BVCONCAT, "concat");
    addMapping(StandardOperation.BVREPEAT, "repeat");
    addMapping(StandardOperation.BVEXTRACT, "extract");
    addMapping(StandardOperation.BVROL, "rotate_left");
    addMapping(StandardOperation.BVROR, "rotate_right");
    addMapping(StandardOperation.BVZEROEXT, "zero_extend");
    addMapping(StandardOperation.BVSIGNEXT, "sign_extend");

    // Bitwise Operations
    addMapping(StandardOperation.BVOR, "bvor");
    addMapping(StandardOperation.BVXOR, "bvxor");
    addMapping(StandardOperation.BVAND, "bvand");
    addMapping(StandardOperation.BVNOT, "bvnot");
    addMapping(StandardOperation.BVNAND, "bvnand");
    addMapping(StandardOperation.BVNOR, "bvnor");
    addMapping(StandardOperation.BVXNOR, "bvxnor");

    // Predicates over Bitvectors
    addMapping(StandardOperation.BVULE, "bvule");
    addMapping(StandardOperation.BVULT, "bvult");
    addMapping(StandardOperation.BVUGE, "bvuge");
    addMapping(StandardOperation.BVUGT, "bvugt");
    addMapping(StandardOperation.BVSLE, "bvsle");
    addMapping(StandardOperation.BVSLT, "bvslt");
    addMapping(StandardOperation.BVSGE, "bvsge");
    addMapping(StandardOperation.BVSGT, "bvsgt");

    /* Array operations */
    addMapping(StandardOperation.SELECT, "select");
    addMapping(StandardOperation.STORE, "store");
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
