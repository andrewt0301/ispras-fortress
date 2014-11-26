/*
 * Copyright 2014 ISP RAS (http://www.ispras.ru)
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

import java.util.IdentityHashMap;
import java.util.Map;

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.transformer.TransformerRule;

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

  protected DependentRule(Map<Enum<?>, TransformerRule> rules) {
    if (rules == null) {
      throw new NullPointerException();
    }
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

  protected final Node reduce(Enum<?> opId, Node ... operands) {
    final Node node = new NodeOperation(opId, operands);
    final TransformerRule rule = rules.get(opId);
    if (rule != null && rule.isApplicable(node)) {
      return rule.apply(node);
    }
    return node;
  }

  abstract public boolean isApplicable(Node node);
  abstract public Node apply(Node node);
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

  public OperationRule(Enum<?> opId, Map<Enum<?>, TransformerRule> rules) {
    super(rules);
    if (opId == null) {
      throw new NullPointerException();
    }
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
  public boolean isApplicable(Node node) {
    return isOperation(node, opId) && isApplicable((NodeOperation) node);
  }

  /**
   * Helper method to allow additional constraints in derived classes.
   * 
   * @return true if derived class accepts given operation node.
   */

  public boolean isApplicable(NodeOperation op) {
    return true;
  }

  public abstract Node apply(Node node);

  /**
   * Helper method to extract operands from node.
   * 
   * @param node Operation node to extract operands from.
   */

  public static Node[] extractOperands(Node node) {
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

  public static boolean isBoolean(Node node) {
    return node.getKind() == Node.Kind.VALUE
      && ((NodeValue) node).getDataType() == DataType.BOOLEAN;
  }

  /**
   * Get boolean value of node in unsafe manner.
   * 
   * @param node NodeValue instance with boolean type.
   * 
   * @return boolean value of given node.
   */

  public static boolean getBoolean(Node node) {
    return (Boolean) ((NodeValue) node).getValue();
  }

  /**
   * Check if node represents specific operation.
   * 
   * @param node Node instance to be checked.
   * @param opId Operation identifier.
   * 
   * @return true if node is NodeOperations instance with given operation id.
   */

  public static boolean isOperation(Node node, Enum<?> opId) {
    return node.getKind() == Node.Kind.OPERATION && ((NodeOperation) node).getOperationId() == opId;
  }

  /**
   * Find first boolean value among operands.
   * 
   * @param op Operation which operands are to be looked.
   * @param start Start looking at operands starting with this index.
   * 
   * @return Operand index of boolean value, -1 if none found.
   */

  public static int booleanOperandIndex(NodeOperation op, int start) {
    for (int i = start; i < op.getOperandCount(); ++i) {
      if (isBoolean(op.getOperand(i))) {
        return i;
      }
    }
    return -1;
  }
}

/**
 * UnrollClause is a helper class implementing standard AND and OR rules.
 */
final class UnrollClause extends OperationRule {
  private final boolean symbol;

  UnrollClause(StandardOperation op, Map<Enum<?>, TransformerRule> rules) {
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
  public boolean isApplicable(NodeOperation in) {
    return booleanOperandIndex(in, 0) >= 0;
  }

  @Override
  public Node apply(Node in) {
    final NodeOperation op = (NodeOperation) in;

    int cnt = 0;
    int pos = booleanOperandIndex(op, 0);
    while (pos >= 0) {
      if (getBoolean(op.getOperand(pos)) == symbol) {
        return op.getOperand(pos);
      }
      pos = booleanOperandIndex(op, pos + 1);
      ++cnt;
    }
    final int effectiveNum = op.getOperandCount() - cnt;
    if (effectiveNum == 0) {
      return op.getOperand(0);
    }
    if (effectiveNum == 1) {
      for (int i = 0; i < op.getOperandCount(); ++i) {
        if (!isBoolean(op.getOperand(i))) {
          return op.getOperand(i);
        }
      }
    }
    int index = 0;
    final Node[] operands = new Node[effectiveNum];
    for (int i = 0; i < op.getOperandCount(); ++i) {
      if (!isBoolean(op.getOperand(i))) {
        operands[index++] = op.getOperand(i);
      }
    }
    return new NodeOperation(getOperationId(), operands);
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
   * (neq ...) -> (not (= ...))
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
   * }
   * </pre>
   *
   */

  public static Map<Enum<?>, TransformerRule> getStandardRuleset() {
    final Map<Enum<?>, TransformerRule> ruleset =
        new IdentityHashMap<Enum<?>, TransformerRule>();

    new OperationRule(StandardOperation.NOTEQ, ruleset) {
      @Override
      public Node apply(Node in) {
        return reduce(StandardOperation.NOT, 
                      reduce(StandardOperation.EQ, extractOperands(in)));
      }
    };

    new OperationRule(StandardOperation.LESSEQ, ruleset) {
      @Override
      public Node apply(Node in) {
        final Node[] operands = extractOperands(in);
        return reduce(StandardOperation.OR,
                      reduce(StandardOperation.LESS, operands),
                      reduce(StandardOperation.EQ, operands));
      }
    };

    new OperationRule(StandardOperation.GREATER, ruleset) {
      @Override
      public Node apply(Node in) {
        final Node[] operands = extractOperands(in);
        return reduce(StandardOperation.AND,
                      reduce(StandardOperation.NOT, reduce(StandardOperation.LESS, operands)),
                      reduce(StandardOperation.NOT, reduce(StandardOperation.EQ, operands)));
      }
    };

    new OperationRule(StandardOperation.GREATEREQ, ruleset) {
      @Override
      public Node apply(Node in) {
        return reduce(StandardOperation.NOT,
                      reduce(StandardOperation.LESS, extractOperands(in)));
      }
    };

    new OperationRule(StandardOperation.BVULE, ruleset) {
      @Override
      public Node apply(Node in) {
        final Node[] operands = extractOperands(in);
        return reduce(StandardOperation.OR, 
                      reduce(StandardOperation.BVULT, operands),
                      reduce(StandardOperation.EQ, operands));
      }
    };

    new OperationRule(StandardOperation.BVUGE, ruleset) {
      @Override
      public Node apply(Node in) {
        return reduce(StandardOperation.NOT,
                      reduce(StandardOperation.BVULT, extractOperands(in)));
      }
    };

    new OperationRule(StandardOperation.BVUGT, ruleset) {
      @Override
      public Node apply(Node in) {
        final Node[] operands = extractOperands(in);
        return reduce(StandardOperation.AND, 
                      reduce(StandardOperation.NOT, reduce(StandardOperation.BVULT, operands)),
                      reduce(StandardOperation.NOT, reduce(StandardOperation.EQ, operands)));
      }
    };

    new OperationRule(StandardOperation.BVSLE, ruleset) {
      @Override
      public Node apply(Node in) {
        final Node[] operands = extractOperands(in);
        return reduce(StandardOperation.OR,
                      reduce(StandardOperation.BVSLT, operands),
                      reduce(StandardOperation.EQ, operands));
      }
    };

    new OperationRule(StandardOperation.BVSGE, ruleset) {
      @Override
      public Node apply(Node in) {
        return reduce(StandardOperation.NOT,
                      reduce(StandardOperation.BVSLT, extractOperands(in)));
      }
    };

    new OperationRule(StandardOperation.BVSGT, ruleset) {
      @Override
      public Node apply(Node in) {
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
      public boolean isApplicable(NodeOperation op) {
        final Node child = op.getOperand(0);
        return isBoolean(child) || isOperation(child, StandardOperation.NOT);
      }

      @Override
      public Node apply(Node in) {
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
      public boolean isApplicable(NodeOperation in) {
        return countImmediateOperands(in) > 1 ||
               booleanOperandIndex(in, 0) >= 0;
      }

      @Override
      public Node apply(Node in) {
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

      private final int countImmediateOperands(NodeOperation node) {
        int n = 0;
        for (int i = 0; i < node.getOperandCount(); ++i) {
          if (node.getOperand(i).getKind() == Node.Kind.VALUE) {
            ++n;
          }
        }
        return n;
      }

      private final Node reduceEqualImmediates(NodeOperation node, int count) {
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

      private final int countEqualImmediates(NodeOperation node) {
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

      private final int immediateIndex(NodeOperation node, int start) {
        for (int i = start; i < node.getOperandCount(); ++i) {
          if (node.getOperand(i).getKind() == Node.Kind.VALUE) {
            return i;
          }
        }
        return -1;
      }

      private final Node reduceBoolean(NodeOperation op, int index) {
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
      public Node apply(Node in) {
        final Node[] operands = extractOperands(in);
        for (int i = 0; i < operands.length - 1; ++i) {
          operands[i] = reduce(StandardOperation.NOT, operands[i]);
        }
        return reduce(StandardOperation.OR, operands);
      }
    };

    return ruleset;
  }
}
