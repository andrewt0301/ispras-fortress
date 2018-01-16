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
import ru.ispras.fortress.expression.Node.Kind;
import ru.ispras.fortress.expression.NodeOperation;

import java.util.ArrayDeque;
import java.util.Deque;

public class TextExprPrinter extends MapBasedPrinter {
  private static final int INDENT = 4;

  public TextExprPrinter() {
    setVisitor(new Visitor());
  }

  protected class Visitor extends ExprTreeVisitor {
    private int depth = 0;
    private final Deque<Boolean> multiline = new ArrayDeque<>();

    @Override
    public void onOperationBegin(final NodeOperation expr) {
      appendText("(");
      appendText(expr.getOperationId().name());

      boolean isMultiline = false;
      for (final Node node : expr.getOperands()) {
        if (node.getKind() == Kind.OPERATION) {
          isMultiline = true;
          break;
        }
      }

      pushMultiline(isMultiline);
    }

    @Override
    public void onOperationEnd(final NodeOperation expr) {
      if (popMultiline()) {
        indent();
      }

      appendText(")");
    }

    @Override
    public int[] getOperandOrder() {
      return null;
    }

    @Override
    public void onOperandBegin(final NodeOperation expr, final Node operand, final int index) {
      if (isMultiline()) {
        indent();
      } else {
        appendText(" ");
      }
    }

    private boolean isMultiline() {
      return multiline.peek();
    }

    private void pushMultiline(final boolean isMultiline) {
      if (isMultiline) {
        depth++;
      }
      multiline.push(isMultiline);
    }

    private boolean popMultiline() {
      final boolean isMultiline = multiline.peek();
      if (isMultiline) {
        depth--;
      }
      multiline.pop();
      return isMultiline;
    }

    private void indent() {
      appendText(System.lineSeparator());
      for (int index = 0; index < depth * INDENT; ++index) {
        appendText(" ");
      }
    }
  }
}
