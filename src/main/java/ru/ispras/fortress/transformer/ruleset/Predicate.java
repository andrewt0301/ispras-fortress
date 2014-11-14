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
 * ExpressionRule is a base class for rules applicable to single operation type.
 */

abstract class ExpressionRule implements TransformerRule {
  private Enum<?> opId;

  /**
   * Create new rule for given operation.
   * 
   * @param opId Operation identifier for this rule.
   */

  public ExpressionRule(Enum<?> opId) {
    if (opId == null) {
      throw new NullPointerException();
    }

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

  public final Node applyOperation(Node ... operands) {
    final Node node = new NodeOperation(this.getOperationId(), operands);
    if (this.isApplicable(node)) {
      return this.apply(node);
    }
    return node;
  }
}

final class UnrollClause extends ExpressionRule {
  private final boolean symbol;

  UnrollClause(StandardOperation op) {
    super(op);
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
   * (neq ...) -> (not (= ...))
   * (<= ...) -> (or (< ...) (= ...))
   * (> ...) -> (and (not (< ...)) (not (= ...)))
   * (>= ...) -> (not (< ...))
   * (not true/false) -> false/true
   * (not (not expr)) -> expr
   * (= true e) -> e0
   * (= false e) -> (not e0)
   * (= true e0 ...) -> (and e0 ...)
   * (= false e0 ...) -> (and (not e0) ...)
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
    final Map<Enum<?>, TransformerRule> ruleset = new IdentityHashMap<Enum<?>, TransformerRule>();

    ExpressionRule rule;

    rule = new ExpressionRule(StandardOperation.NOTEQ) {
      @Override
      public Node apply(Node in) {
        return new NodeOperation(StandardOperation.NOT, new NodeOperation(StandardOperation.EQ,
            extractOperands(in)));
      }
    };
    ruleset.put(rule.getOperationId(), rule);

    rule = new ExpressionRule(StandardOperation.LESSEQ) {
      @Override
      public Node apply(Node in) {
        Node[] operands = extractOperands(in);
        return new NodeOperation(StandardOperation.OR, new NodeOperation(StandardOperation.LESS,
            operands), new NodeOperation(StandardOperation.EQ, operands));
      }
    };
    ruleset.put(rule.getOperationId(), rule);

    rule = new ExpressionRule(StandardOperation.GREATER) {
      @Override
      public Node apply(Node in) {
        Node[] operands = extractOperands(in);
        return new NodeOperation(StandardOperation.AND, new NodeOperation(StandardOperation.NOT,
            new NodeOperation(StandardOperation.LESS, operands)), new NodeOperation(
            StandardOperation.NOT, new NodeOperation(StandardOperation.EQ, operands)));
      }
    };
    ruleset.put(rule.getOperationId(), rule);

    rule = new ExpressionRule(StandardOperation.GREATEREQ) {
      @Override
      public Node apply(Node in) {
        return new NodeOperation(StandardOperation.NOT, new NodeOperation(StandardOperation.LESS,
            extractOperands(in)));
      }
    };
    ruleset.put(rule.getOperationId(), rule);

    rule = new ExpressionRule(StandardOperation.BVULE) {
      @Override
      public Node apply(Node in) {
        Node[] operands = extractOperands(in);
        return new NodeOperation(StandardOperation.OR, new NodeOperation(StandardOperation.BVULT,
            operands), new NodeOperation(StandardOperation.EQ, operands));
      }
    };
    ruleset.put(rule.getOperationId(), rule);

    rule = new ExpressionRule(StandardOperation.BVUGE) {
      @Override
      public Node apply(Node in) {
        return new NodeOperation(StandardOperation.NOT, new NodeOperation(StandardOperation.BVULT,
            extractOperands(in)));
      }
    };
    ruleset.put(rule.getOperationId(), rule);

    rule = new ExpressionRule(StandardOperation.BVUGT) {
      @Override
      public Node apply(Node in) {
        Node[] operands = extractOperands(in);
        return new NodeOperation(StandardOperation.AND, new NodeOperation(StandardOperation.NOT,
            new NodeOperation(StandardOperation.BVULT, operands)), new NodeOperation(
            StandardOperation.NOT, new NodeOperation(StandardOperation.EQ, operands)));
      }
    };
    ruleset.put(rule.getOperationId(), rule);

    rule = new ExpressionRule(StandardOperation.BVSLE) {
      @Override
      public Node apply(Node in) {
        Node[] operands = extractOperands(in);
        return new NodeOperation(StandardOperation.OR, new NodeOperation(StandardOperation.BVSLT,
            operands), new NodeOperation(StandardOperation.EQ, operands));
      }
    };
    ruleset.put(rule.getOperationId(), rule);

    rule = new ExpressionRule(StandardOperation.BVSGE) {
      @Override
      public Node apply(Node in) {
        return new NodeOperation(StandardOperation.NOT, new NodeOperation(StandardOperation.BVSLT,
            extractOperands(in)));
      }
    };
    ruleset.put(rule.getOperationId(), rule);

    rule = new ExpressionRule(StandardOperation.BVSGT) {
      @Override
      public Node apply(Node in) {
        Node[] operands = extractOperands(in);
        return new NodeOperation(StandardOperation.AND, new NodeOperation(StandardOperation.NOT,
            new NodeOperation(StandardOperation.BVSLT, operands)), new NodeOperation(
            StandardOperation.NOT, new NodeOperation(StandardOperation.EQ, operands)));
      }
    };
    ruleset.put(rule.getOperationId(), rule);


    // (not true/false) -> false/true
    // (not (not expr)) -> expr
    final ExpressionRule unrollNotRule = new ExpressionRule(StandardOperation.NOT) {
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
    ruleset.put(unrollNotRule.getOperationId(), unrollNotRule);

    final ExpressionRule conjunctionRule = new UnrollClause(StandardOperation.AND);
    ruleset.put(conjunctionRule.getOperationId(), conjunctionRule);

    final ExpressionRule disjunctionRule = new UnrollClause(StandardOperation.OR);
    ruleset.put(disjunctionRule.getOperationId(), disjunctionRule);

    // (eq expr true) -> expr
    // (eq expr false) -> (not expr)
    // (eq true expr0 ...) -> (and expr0 ...)
    // (eq false expr0 ...) -> (and (not expr0) ...)
    rule = new ExpressionRule(StandardOperation.EQ) {
      @Override
      public boolean isApplicable(NodeOperation in) {
        return booleanOperandIndex(in, 0) >= 0;
      }

      @Override
      public Node apply(Node in) {
        final NodeOperation op = (NodeOperation) in;
        final int index = booleanOperandIndex(op, 0);
        final boolean value = ((Boolean) ((NodeValue) op.getOperand(index)).getValue());

        // For simple equalities just return plain or negated expression
        if (op.getOperandCount() == 2) {
          final Node node = op.getOperand((index + 1) % 2);
          return (value) ? node : unrollNotRule.applyOperation(node);
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
            operands[i] = unrollNotRule.applyOperation(operands[i]);
          }
        }
        return conjunctionRule.applyOperation(operands);
      }
    };
    ruleset.put(rule.getOperationId(), rule);

    rule = new ExpressionRule(StandardOperation.IMPL) {
      @Override
      public Node apply(Node in) {
        final Node[] operands = extractOperands(in);
        for (int i = 0; i < operands.length - 1; ++i) {
          operands[i] = unrollNotRule.applyOperation(operands[i]);
        }
        return disjunctionRule.applyOperation(operands);
      }
    };
    ruleset.put(rule.getOperationId(), rule);

    return ruleset;
  }
}
