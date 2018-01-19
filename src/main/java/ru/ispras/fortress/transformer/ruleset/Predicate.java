/*
 * Copyright 2014-2018 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.transformer.ruleset;

import ru.ispras.fortress.expression.ExprUtils;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.transformer.TransformerRule;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;

/**
 * The Predicate class provides static methods to create predefined transformation rulesets to use
 * with {@link ru.ispras.fortress.transformer.NodeTransformer NodeTransformer}.
 */
public final class Predicate {
  private Predicate() {}

  /**
   * Create ruleset for standard predicate transformations.
   * Complete list of transformations is as follows:
   * <pre>
   * {@code
   * en - expression, cn - constant
   * (neq x y z ...) -> (and (not (= x y)) (not (= x z)) (not (= y z)) ...)
   * (<= ...) -> (or (< ...) (= ...))
   * (> ...) -> (and (not (< ...)) (not (= ...)))
   * (>= ...) -> (not (< ...))
   * (not true/false) -> false/true
   * (not (not expr)) -> expr
   * (= true e) -> e
   * (= false e) -> (not e)
   * (= true e0 ...) -> (and e0 ...)
   * (= false e0 ...) -> (and (not e0) ...)
   * (= c0 c0 e0 ...) -> (= c0 ...)
   * (= c0 c1 e1 ...) -> false
   * (= c0 c0 ... c0) -> true
   * (=> e0 ... en) -> (or (not e0) ... en)
   * (and false ...) -> false
   * (and true ...) -> (and ...)
   * (or true ...) -> true
   * (or false ...) -> (or ...)
   * (ite true e0 e1) -> e0
   * (ite false e0 e1) -> e1
   * }
   * </pre>
   *
   * @return Map of transformer rulers.
   */
  public static Map<Enum<?>, TransformerRule> getStandardRuleset() {
    final Map<Enum<?>, TransformerRule> ruleset = new IdentityHashMap<>();

    new OperationRule(StandardOperation.NOTEQ, ruleset) {
      @Override
      public Node apply(final NodeOperation in) {
        final int n = in.getOperandCount();
        final List<Node> pairwise = new ArrayList<>(n * (n - 1));
        for (int i = 0; i < in.getOperandCount() - 1; ++i) {
          final Node lhs = in.getOperand(i);
          for (int j = i + 1; j < in.getOperandCount(); ++j) {
            final Node eq = reduce(StandardOperation.EQ, lhs, in.getOperand(j));
            pairwise.add(reduce(StandardOperation.NOT, eq));
          }
        }
        return reduce(StandardOperation.AND, pairwise);
      }
    };

    new OperationRule(StandardOperation.LESSEQ, ruleset) {
      @Override
      public Node apply(final NodeOperation in) {
        final Node[] operands = extractOperands(in);
        return reduce(StandardOperation.OR,
                      reduce(StandardOperation.LESS, operands),
                      reduce(StandardOperation.EQ, operands));
      }
    };

    new OperationRule(StandardOperation.GREATER, ruleset) {
      @Override
      public Node apply(final NodeOperation in) {
        final Node[] operands = extractOperands(in);
        return reduce(StandardOperation.AND,
                      reduce(StandardOperation.NOT, reduce(StandardOperation.LESS, operands)),
                      reduce(StandardOperation.NOT, reduce(StandardOperation.EQ, operands)));
      }
    };

    new OperationRule(StandardOperation.GREATEREQ, ruleset) {
      @Override
      public Node apply(final NodeOperation in) {
        return reduce(StandardOperation.NOT,
                      reduce(StandardOperation.LESS, extractOperands(in)));
      }
    };

    new OperationRule(StandardOperation.BVULE, ruleset) {
      @Override
      public Node apply(final NodeOperation in) {
        final Node[] operands = extractOperands(in);
        return reduce(StandardOperation.OR, 
                      reduce(StandardOperation.BVULT, operands),
                      reduce(StandardOperation.EQ, operands));
      }
    };

    new OperationRule(StandardOperation.BVUGE, ruleset) {
      @Override
      public Node apply(final NodeOperation in) {
        return reduce(StandardOperation.NOT,
                      reduce(StandardOperation.BVULT, extractOperands(in)));
      }
    };

    new OperationRule(StandardOperation.BVUGT, ruleset) {
      @Override
      public Node apply(final NodeOperation in) {
        final Node[] operands = extractOperands(in);
        return reduce(StandardOperation.AND, 
                      reduce(StandardOperation.NOT, reduce(StandardOperation.BVULT, operands)),
                      reduce(StandardOperation.NOT, reduce(StandardOperation.EQ, operands)));
      }
    };

    new OperationRule(StandardOperation.BVSLE, ruleset) {
      @Override
      public Node apply(final NodeOperation in) {
        final Node[] operands = extractOperands(in);
        return reduce(StandardOperation.OR,
                      reduce(StandardOperation.BVSLT, operands),
                      reduce(StandardOperation.EQ, operands));
      }
    };

    new OperationRule(StandardOperation.BVSGE, ruleset) {
      @Override
      public Node apply(final NodeOperation in) {
        return reduce(StandardOperation.NOT,
                      reduce(StandardOperation.BVSLT, extractOperands(in)));
      }
    };

    new OperationRule(StandardOperation.BVSGT, ruleset) {
      @Override
      public Node apply(final NodeOperation in) {
        final Node[] operands = extractOperands(in);
        return reduce(StandardOperation.AND,
                      reduce(StandardOperation.NOT, reduce(StandardOperation.BVSLT, operands)),
                      reduce(StandardOperation.NOT, reduce(StandardOperation.EQ, operands)));
      }
    };

    // (not true/false) -> false/true
    // (not (not expr)) -> expr
    new OperationRule(StandardOperation.NOT, ruleset) {
      @Override
      public boolean isApplicable(final NodeOperation op) {
        final Node child = op.getOperand(0);
        return isBoolean(child) || ExprUtils.isOperation(child, StandardOperation.NOT);
      }

      @Override
      public Node apply(final NodeOperation in) {
        final Node child = ((NodeOperation) in).getOperand(0);

        if (isBoolean(child)) {
          final Node neg = NodeValue.newBoolean(!getBoolean(child));
          neg.setUserData(child.getUserData());
          return neg;
        }
        return ((NodeOperation) child).getOperand(0);
      }
    };

    new UnrollClause(StandardOperation.AND, ruleset);
    new UnrollClause(StandardOperation.OR, ruleset);

    // (eq expr true) -> expr
    // (eq expr false) -> (not expr)
    // (eq true expr0 ...) -> (and expr0 ...)
    // (eq false expr0 ...) -> (and (not expr0) ...)
    new OperationRule(StandardOperation.EQ, ruleset) {
      @Override
      public boolean isApplicable(final NodeOperation in) {
        return countImmediateOperands(in) > 1 || booleanOperandIndex(in, 0) >= 0;
      }

      @Override
      public Node apply(final NodeOperation in) {
        final NodeOperation op = (NodeOperation) in;

        final int count = countEqualImmediates(op);
        if (count < 0) {
          return NodeValue.newBoolean(false);
        }
        if (count == op.getOperandCount()) {
          return NodeValue.newBoolean(true);
        }
        if (count > 1) {
          return reduceEqualImmediates(op, count);
        }
        return reduceBoolean(op, booleanOperandIndex(op, 0));
      }

      private int countImmediateOperands(final NodeOperation node) {
        int count = 0;
        for (int i = 0; i < node.getOperandCount(); ++i) {
          if (node.getOperand(i).getKind() == Node.Kind.VALUE) {
            ++count;
          }
        }
        return count;
      }

      private Node reduceEqualImmediates(final NodeOperation node, final int count) {
        final Node[] operands = new Node[node.getOperandCount() - count + 1];
        final Node immediate = node.getOperand(immediateIndex(node, 0));
        operands[0] = immediate;

        int index = 1;
        for (int i = 0; i < node.getOperandCount(); ++i) {
          final Node operand = node.getOperand(i);
          if (operand.getKind() == Node.Kind.VALUE) {
            continue;
          }
          operands[index++] = operand;
        }
        final NodeOperation reduced =
            new NodeOperation(StandardOperation.EQ, operands);

        if (isBoolean(immediate)) {
          return reduceBoolean(reduced, 0);
        }
        return reduced;
      }

      private int countEqualImmediates(final NodeOperation node) {
        int index = immediateIndex(node, 0);
        final Node immediate = node.getOperand(index);

        int count = 0;
        while (index >= 0) {
          if (!node.getOperand(index).equals(immediate)) {
            return -1;
          }
          index = immediateIndex(node, index + 1);
          ++count;
        }
        return count;
      }

      private int immediateIndex(final NodeOperation node, final int start) {
        for (int i = start; i < node.getOperandCount(); ++i) {
          if (node.getOperand(i).getKind() == Node.Kind.VALUE) {
            return i;
          }
        }
        return -1;
      }

      private Node reduceBoolean(final NodeOperation op, final int index) {
        final boolean value = ((Boolean) ((NodeValue) op.getOperand(index)).getValue());

        // For simple equalities just return plain or negated expression
        if (op.getOperandCount() == 2) {
          final Node node = op.getOperand((index + 1) % 2);
          return (value) ? node : reduce(StandardOperation.NOT, node);
        }

        // Chained equality with known boolean is conjunction of
        // plain or negated expressions.
        final Node[] operands = new Node[op.getOperandCount() - 1];
        for (int i = 0; i < index; ++i) {
          operands[i] = op.getOperand(i);
        }
        for (int i = index + 1; i < op.getOperandCount(); ++i) {
          operands[i - 1] = op.getOperand(i);
        }
        if (!value) {
          for (int i = 0; i < operands.length; ++i) {
            operands[i] = reduce(StandardOperation.NOT, operands[i]);
          }
        }
        return reduce(StandardOperation.AND, operands);
      }
    };

    new OperationRule(StandardOperation.IMPL, ruleset) {
      @Override
      public Node apply(final NodeOperation in) {
        final Node[] operands = extractOperands(in);
        for (int i = 0; i < operands.length - 1; ++i) {
          operands[i] = reduce(StandardOperation.NOT, operands[i]);
        }
        return reduce(StandardOperation.OR, operands);
      }
    };

    new OperationRule(StandardOperation.ITE, ruleset) {
      @Override
      public boolean isApplicable(final NodeOperation ite) {
        return isBoolean(ite.getOperand(0));
      }

      @Override
      public Node apply(final NodeOperation node) {
        final NodeOperation ite = (NodeOperation) node;
        if (getBoolean(ite.getOperand(0))) {
          return ite.getOperand(1);
        }
        return ite.getOperand(2);
      }
    };

    return ruleset;
  }
}
