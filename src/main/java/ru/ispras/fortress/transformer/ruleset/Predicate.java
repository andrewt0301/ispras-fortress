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

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.expression.ExprUtils;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.transformer.TransformerRule;
import ru.ispras.fortress.util.InvariantChecks;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

/**
 * DependentRule is a base class for rules dedicated for use in set.
 */
abstract class DependentRule implements TransformerRule {
  private final Map<Enum<?>, TransformerRule> rules;

  /**
   * Create rule for use in set.
   *
   * @param rules Ruleset shared by all interdependent rules.
   */
  protected DependentRule(final Map<Enum<?>, TransformerRule> rules) {
    InvariantChecks.checkNotNull(rules);
    this.rules = rules;
  }

  /**
   * Create expression from operation applying rules from shared set.
   *
   * @param opId Operation identifier.
   * @param operands Operation operands.
   *
   * @return Node instance which is expression resulted from recursively
   * applying relevant rules in shared set to single operation.
   */
  protected final Node reduce(final Enum<?> opId, final Node ... operands) {
    final Node node = new NodeOperation(opId, operands);
    final TransformerRule rule = rules.get(opId);
    if (rule != null && rule.isApplicable(node)) {
      return rule.apply(node);
    }
    return node;
  }

  protected final Node reduce(final Enum<?> opId, final Collection<? extends Node> operands) {
    return reduce(opId, operands.toArray(new Node[operands.size()]));
  }

  public abstract boolean isApplicable(Node node);

  public abstract Node apply(Node node);
}

/**
 * OperationRule is a base class for rules applicable to single operation type.
 */
abstract class OperationRule extends DependentRule {
  private final Enum<?> opId;

  /**
   * Create new rule for given operation and register in given ruleset.
   * 
   * @param opId Operation identifier for this rule.
   * @param rules Ruleset to register the rule in.
   */
  public OperationRule(final Enum<?> opId, final Map<Enum<?>, TransformerRule> rules) {
    super(rules);
    InvariantChecks.checkNotNull(opId);

    if (rules.containsKey(opId)) {
      throw new IllegalArgumentException("Attempt to override " + opId + " rule");
    }
    // side-effects... saves quite a bit of typing though and provides
    // minor correctness guarantees
    rules.put(opId, this);

    this.opId = opId;
  }

  /**
   * Get operation identifier for this rule.
   */

  public Enum<?> getOperationId() {
    return opId;
  }

  @Override
  public boolean isApplicable(final Node node) {
    return ExprUtils.isOperation(node, opId) && isApplicable((NodeOperation) node);
  }

  /**
   * Helper method to allow additional constraints in derived classes.
   * 
   * @return true if derived class accepts given operation node.
   */
  public boolean isApplicable(final NodeOperation op) {
    return true;
  }

  @Override
  public final Node apply(final Node node) {
    return apply((NodeOperation) node);
  }

  public abstract Node apply(NodeOperation node);

  /**
   * Helper method to extract operands from node.
   * 
   * @param node Operation node to extract operands from.
   */
  public static Node[] extractOperands(final Node node) {
    final NodeOperation in = (NodeOperation) node;
    final Node[] operands = new Node[in.getOperandCount()];

    for (int i = 0; i < operands.length; ++i) {
      operands[i] = in.getOperand(i);
    }

    return operands;
  }

  /**
   * Check if node represents boolean value.
   * 
   * @param node Node instance to be checked.
   * 
   * @return true if node is NodeValue instance with boolean type.
   */
  public static boolean isBoolean(final Node node) {
    return node.getKind() == Node.Kind.VALUE
      && node.getDataType() == DataType.BOOLEAN;
  }

  /**
   * Get boolean value of node in unsafe manner.
   * 
   * @param node NodeValue instance with boolean type.
   * 
   * @return boolean value of given node.
   */

  public static boolean getBoolean(final Node node) {
    return (Boolean) ((NodeValue) node).getValue();
  }

  /**
   * Find first boolean value among operands.
   *
   * @param op Operation which operands are to be looked.
   * @param start Start looking at operands starting with this index.
   *
   * @return Operand index of boolean value, -1 if none found.
   */
  public static int booleanOperandIndex(final NodeOperation op, int start) {
    for (int i = start; i < op.getOperandCount(); ++i) {
      if (isBoolean(op.getOperand(i))) {
        return i;
      }
    }
    return -1;
  }

  static boolean isDistinct(final Node node) {
    return getDistinct(node) != null;
  }

  static NodeOperation getDistinct(final Node node) {
    if (ExprUtils.isOperation(node, StandardOperation.NOTEQ)) {
      return (NodeOperation) node;
    }
    final List<Node> operands = getNotEqOperands(node);
    if (operands.size() == 2) {
      return new NodeOperation(StandardOperation.NOTEQ, operands);
    }
    return null;
  }

  private static List<Node> getNotEqOperands(final Node node) {
    if (ExprUtils.isOperation(node, StandardOperation.NOT)) {
      final Node child = ((NodeOperation) node).getOperand(0);
      if (ExprUtils.isOperation(child, StandardOperation.EQ)) {
        return ((NodeOperation) child).getOperands();
      }
    }
    return Collections.emptyList();
  }
}

/**
 * UnrollClause is a helper class implementing standard AND and OR rules.
 */
final class UnrollClause extends OperationRule {
  private final boolean symbol;

  UnrollClause(final StandardOperation op, final Map<Enum<?>, TransformerRule> rules) {
    super(op, rules);
    if (op == StandardOperation.AND) {
      this.symbol = false;
    } else if (op == StandardOperation.OR) {
      this.symbol = true;
    } else {
      throw new IllegalArgumentException();
    }
  }
  
  @Override
  public boolean isApplicable(final NodeOperation in) {
    for (int i = 0; i < in.getOperandCount(); ++i) {
      final Node operand = in.getOperand(i);
      if (isBoolean(operand)
          || ExprUtils.isOperation(operand, this.getOperationId()) ||
          appliesTo(operand)) {
        return true;
      }
    }
    return false;
  }

  private boolean appliesTo(final Node node) {
    if (getOperationId().equals(StandardOperation.AND)) {
      return ExprUtils.isOperation(node, StandardOperation.EQ) || isDistinct(node);
    }
    return false;
  }

  @Override
  public Node apply(final NodeOperation op) {
    int numBoolean = 0;
    for (final Node operand : op.getOperands()) {
      if (isBoolean(operand)) {
        if (getBoolean(operand) == this.symbol) {
          return operand;
        } else {
          ++numBoolean;
        }
      }
    }
    if (numBoolean == op.getOperandCount()) {
      return op.getOperand(0);
    }
    final List<Node> operands = this.flattenFilter(op);
    if (!this.postprocess(operands)) {
      return NodeValue.newBoolean(false);
    }
    if (operands.size() == 1) {
      return operands.get(0);
    }
    return new NodeOperation(this.getOperationId(), operands);
  }

  private List<Node> flattenFilter(final NodeOperation op) {
    final List<Node> operands = new ArrayList<>(op.getOperandCount());
    this.flattenFilter(op, operands);
    return operands;
  }

  private void flattenFilter(final NodeOperation op, final List<Node> operands) {
    for (final Node operand : op.getOperands()) {
      if (ExprUtils.isOperation(operand, this.getOperationId())) {
        this.flattenFilter((NodeOperation) operand, operands);
      } else if (!isBoolean(operand)) {
        operands.add(operand);
      }
    }
  }

  private boolean postprocess(final List<Node> operands) {
    if (this.getOperationId() != StandardOperation.AND) {
      return true;
    }

    final EqualityConstraint constraint = filterEqualities(operands);
    if (constraint.isEmpty()) {
      return true;
    }

    final List<Node> reduced = constraint.reduce();
    if (reduced.isEmpty()) { // everything is (eq x x)
      return true;
    }
    if (reduced.size() == 1 && isBoolean(reduced.get(0))) {
      return getBoolean(reduced.get(0));
    }
    operands.addAll(reduced);

    return true;
  }

  private static EqualityConstraint filterEqualities(
      final Collection<? extends Node> operands) {

    final EqualityConstraint constraint = new EqualityConstraint();

    final Iterator<? extends Node> it = operands.iterator();
    while (it.hasNext()) {
      final Node operand = it.next();
      if (ExprUtils.isOperation(operand, StandardOperation.EQ)) {
        constraint.addEquality(operand);
        it.remove();
      } else if (isDistinct(operand)) {
        constraint.addInequality(getDistinct(operand));
        it.remove();
      }
    }
    return constraint;
  }
}

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
        int n = 0;
        for (int i = 0; i < node.getOperandCount(); ++i) {
          if (node.getOperand(i).getKind() == Node.Kind.VALUE) {
            ++n;
          }
        }
        return n;
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
