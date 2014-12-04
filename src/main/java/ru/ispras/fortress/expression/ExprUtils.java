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

package ru.ispras.fortress.expression;

import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.expression.ExprTreeVisitor.Status;
import ru.ispras.fortress.solver.SolverResult;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintUtils;

/**
 * The ExprUtils class provides utility methods to work with logical expressions.
 * 
 * @author Andrei Tatarnikov
 */

public final class ExprUtils {
  private ExprUtils() {}

  /**
   * Checks whether the specified expression is a logical expression (can be evaluated to boolean).
   * 
   * @param expr Expression to be checked.
   * @return {@code true} if the expression is logical (can be evaluated to boolean) or
   *         {@code false} otherwise.
   * 
   * @throws NullPointerException if the parameter is {@code null}.
   */

  public static boolean isCondition(Node expr) {
    checkNotNull(expr);
    return expr.getDataType().equals(DataType.BOOLEAN);
  }

  /**
   * Checks whether the specified expression is an atomic logical expression (can be evaluated to
   * boolean and does not include logical operations to combine expressions such as: AND, OR, NOT,
   * XOR and IMPL).
   * 
   * @param expr Expression to be checked.
   * @return {@code true} if the expression is an atomic logical expression or {@code false}
   *         otherwise.
   * 
   * @throws NullPointerException if the parameter is {@code null}.
   */

  public static boolean isAtomicCondition(Node expr) {
    if (!isCondition(expr)) {
      return false;
    }

    final Set<StandardOperation> logicOperations =
        EnumSet.of(StandardOperation.AND, StandardOperation.OR, StandardOperation.NOT,
            StandardOperation.XOR, StandardOperation.IMPL);

    final ExprTreeVisitor visitor = new ExprTreeVisitorDefault() {
      @Override
      public void onOperationBegin(NodeOperation node) {
        if (logicOperations.contains(node.getOperationId())) {
          setStatus(Status.ABORT);
        }
      }
    };

    final ExprTreeWalker walker = new ExprTreeWalker(visitor);
    walker.visit(expr);

    return visitor.getStatus() == Status.OK;
  }

  /**
   * Checks whether the specified expression tree contains bindings (nodes of type BINDING).
   * 
   * @param expr Expression to be checked.
   * @return {@code true} if the expression tree contains bindings (nodes of type BINDING) or
   *         {@code false} otherwise.
   * 
   * @throws NullPointerException if the parameter is {@code null}.
   */

  public static boolean hasBindings(Node expr) {
    checkNotNull(expr);

    final ExprTreeVisitor visitor = new ExprTreeVisitorDefault() {
      @Override
      public void onBindingBegin(NodeBinding node) {
        setStatus(Status.ABORT);
      }
    };

    final ExprTreeWalker walker = new ExprTreeWalker(visitor);
    walker.visit(expr);

    return visitor.getStatus() == Status.ABORT;
  }

  /**
   * Checks whether the given expression is a constant expression (can be evaluated to a constant
   * value). An expression is considered constant as long as it does not contain unassigned
   * variables (bindings are taken into consideration).
   * 
   * @param expr Expression to be checked.
   * @return {@code true} if the expression is a constant expression or {@code false} otherwise.
   * 
   * @throws NullPointerException if the parameter is {@code null}.
   */

  public static boolean isConstant(Node expr) {
    checkNotNull(expr);

    final ExprTreeVisitor visitor = new ExprTreeVisitorDefault() {
      // Variables bound to constant values (a stack of scopes).
      private final Deque<Set<String>> knownVariables = new LinkedList<Set<String>>();

      @Override
      public void onVariable(NodeVariable variable) {
        if (variable.getVariable().hasValue()) {
          return;
        }

        for (Set<String> scope : knownVariables) {
          if (scope.contains(variable.getName())) {
            return;
          }
        }

        setStatus(Status.ABORT);
      }

      @Override
      public void onBindingBegin(NodeBinding node) {
        knownVariables.push(new HashSet<String>());
      }

      @Override
      public void onBindingEnd(NodeBinding node) {
        knownVariables.pop();
      }

      @Override
      public void onBoundVariableEnd(NodeBinding node, NodeVariable variable, Node value) {
        final Set<String> currentScope = knownVariables.peek();
        currentScope.add(variable.getName());
      }
    };

    final ExprTreeWalker walker = new ExprTreeWalker(visitor);
    walker.visit(expr);

    return visitor.getStatus() == Status.OK;
  }

  /**
   * Performs logical conjunction {@code (exprs[0] && ... && exprs[n-1])} of the specified
   * expressions and returns the resulting expression.
   * 
   * @param exprs Expressions to be combined.
   * @return A logical conjunction of the specified expressions.
   * 
   * @throws IllegalArgumentException if no arguments are provided; if an argument is not a logical
   *         expression.
   * @throws NullPointerException if any argument in the array is {@code null}.
   */

  public static Node getConjunction(Node... exprs) {
    checkNotEmpty(exprs);
    checkAllConditions(exprs);

    if (exprs.length == 1) {
      return exprs[0];
    }

    return new NodeOperation(StandardOperation.AND, exprs);
  }

  /**
   * Performs logical disjunction {@code (exprs[0] || ... || exprs[n-1])} of the specified
   * expressions and returns the resulting expression.
   * 
   * @param exprs Expressions to be combined.
   * @return A logical disjunction of the specified expressions.
   * 
   * @throws IllegalArgumentException if no arguments are provided; if an argument is not a logical
   *         expression.
   * @throws NullPointerException if any argument in the array is {@code null}.
   */

  public static Node getDisjunction(Node... exprs) {
    checkNotEmpty(exprs);
    checkAllConditions(exprs);

    if (exprs.length == 1) {
      return exprs[0];
    }

    return new NodeOperation(StandardOperation.OR, exprs);
  }

  /**
   * Performs logical negation {@code (!getConjunction(exprs[0], ..., exprs[n-1]))} of the specified
   * expressions combined with conjunction and returns the resulting expression.
   * 
   * @param exprs Expressions to be combined.
   * @return A logical negation of the specified expressions.
   * 
   * @throws IllegalArgumentException if no arguments are provided; if an argument is not a logical
   *         expression.
   * @throws NullPointerException if any argument in the array is {@code null}.
   */

  public static Node getNegation(Node... exprs) {
    return new NodeOperation(StandardOperation.NOT, getConjunction(exprs));
  }

  /**
   * Performs logical complement (negation) {@code !(getDisjunction(exprs[0], ..., exprs[n-1])} of
   * the specified expressions combined with disjunction and returns the resulting expression.
   * 
   * @param exprs Expressions to be combined.
   * @return A logical complement of the specified expressions.
   * 
   * @throws IllegalArgumentException if no arguments are provided; if an argument is not a logical
   *         expression.
   * @throws NullPointerException if any argument in the array is {@code null}.
   */

  public static Node getComplement(Node... exprs) {
    return new NodeOperation(StandardOperation.NOT, getDisjunction(exprs));
  }

  /**
   * Checks whether the specified logical conditions are complete
   * {@code !(getComplement(exprs[0], ..., exprs[n-1]) is SAT)}. N.B. The method uses the default
   * constraint solver to perform the check.
   * 
   * @param exprs Conditions (logical expressions) to be checked.
   * @return {@code true} if the conditions are complete or {@code false} otherwise.
   * 
   * @throws IllegalArgumentException if no arguments are provided; if an argument is not a logical
   *         expression.
   * @throws NullPointerException if any argument in the array is {@code null}.
   */

  public static boolean areComplete(Node... exprs) {
    final Node target = getComplement(exprs);

    return !isSAT(target);
  }

  /**
   * Checks whether the specified logical conditions are compatible
   * {@code (getConjunction(exprs[0], ..., exprs[n-1]) is SAT)}. N.B. The method uses the default
   * constraint solver to perform the check.
   * 
   * @param exprs Conditions (logical expressions) to be checked.
   * @return {@code true} if the conditions are compatible or {@code false} otherwise.
   * 
   * @throws IllegalArgumentException if no arguments are provided; if an argument is not a logical
   *         expression.
   * @throws NullPointerException if any argument in the array is {@code null}.
   */

  public static boolean areCompatible(Node... exprs) {
    final Node target = getConjunction(exprs);

    return isSAT(target);
  }

  /**
   * Checks whether the specified expression is satisfiable. N.B. The method uses the default
   * constraint solver to perform the check.
   * 
   * @param expr Expression to be checked.
   * @return {@code true} if the expression is satisfiable or {@code false} otherwise.
   * 
   * @throws NullPointerException if the parameter is {@code null}.
   * @throws IllegalArgumentException (1) if the expression description contains errors that
   * prevent the solver engine from solving it in a correct way or (2) if the solver is unable
   * to solve a constraint based on the given expression due to limitations of its implementation.
   * @throws IllegalStateException if the solver engine returned results with an unknown status.    
   */

  public static boolean isSAT(Node expr) {
    final Constraint constraint = ConstraintUtils.newConstraint(expr);
    final SolverResult result = ConstraintUtils.solve(constraint);

    switch (result.getStatus()) {
      case SAT:
        return true;

      case UNSAT:
        return false;

      case ERROR:
        throw new IllegalArgumentException(String.format(
            "Errors in the expression description: %s", result.getErrors()));

      case UNKNOWN:
        throw new IllegalArgumentException(String.format(
            "Unable to solve a constraint based on the given expression: %s", result.getErrors()));

      default:
        throw new IllegalStateException(String.format(
            "The solver returned incorrect status %s: %s", result.getStatus(), result.getErrors()));
    }
  }

  /**
   * Returns all variables used in the specified expression.
   * 
   * @param expr Expression to be processed.
   * @return A collection of all variables used in the specified expression.
   * 
   * @throws NullPointerException if the parameter is {@code null}.
   * @throws IllegalStateException if the method finds nodes that refer to different variables that
   *         have the same name.
   */

  public static Collection<NodeVariable> getVariables(Node expr) {
    checkNotNull(expr);
    return getVariables(Collections.singletonList(expr));
  }

  /**
   * Returns all variables used in the specified expressions.
   * 
   * @param exprs Collection of expressions to be processed.
   * @return A collection of all variables used in the specified expressions.
   * 
   * @throws NullPointerException if the parameter is {@code null}.
   * @throws IllegalStateException if the method finds nodes that refer to different variables that
   *         have the same name.
   */

  public static Collection<NodeVariable> getVariables(Iterable<Node> exprs) {
    checkNotNull(exprs);

    final String ERR_MULTIPLE_VARS =
        "References to different variables that have the same name %s.";

    final Map<String, NodeVariable> variables = new HashMap<String, NodeVariable>();
    final ExprTreeWalker walker = new ExprTreeWalker(new ExprTreeVisitorDefault() {
      @Override
      public void onVariable(NodeVariable variable) {
        checkNotNull(variable);
        final String name = variable.getName();

        if (variables.containsKey(name)) {
          final NodeVariable existingVariable = variables.get(name);
          if (!variable.equals(existingVariable)) {
            throw new IllegalStateException(String.format(ERR_MULTIPLE_VARS, name));
          }
        } else {
          variables.put(name, variable);
        }
      }
    });

    walker.visit(exprs);
    return variables.values();
  }

  private static void checkNotNull(Object o) {
    if (null == o) {
      throw new NullPointerException();
    }
  }

  private static void checkNotEmpty(Node... exprs) {
    if (0 == exprs.length) {
      throw new IllegalArgumentException("No expressions are provided.");
    }
  }

  private static void checkAllConditions(Node... exprs) {
    for (Node expr : exprs) {
      if (!isCondition(expr)) {
        throw new IllegalArgumentException("Expression is not a condition: " + expr.toString());
      }
    }
  }
}
