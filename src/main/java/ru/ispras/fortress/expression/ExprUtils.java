/*
 * Copyright 2014-2017 ISP RAS (http://www.ispras.ru)
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
import ru.ispras.fortress.data.DataTypeId;
import ru.ispras.fortress.util.TreeVisitor.Status;
import ru.ispras.fortress.solver.SolverResult;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintUtils;
import ru.ispras.fortress.util.InvariantChecks;

/**
 * The {@link ExprUtils} class provides utility methods to work with logical expressions.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public final class ExprUtils {
  private ExprUtils() {}

  /**
   * Checks whether all of the specified expressions have the specified type
   * (types are compared on the {@link DataTypeId} level).
   *
   * @param typeId Expected data type identifier.
   * @param exprs Expressions to be checked.
   * @return {@code true} if all expression types match the type specified by
   * the {@code typeId} argument or {@code false} otherwise.
   *
   * @throws IllegalArgumentException if the expression array is empty;
   *         if any expression in the array is {@code null}.
   */
  public static boolean isType(final DataTypeId typeId, final Node... exprs) {
    InvariantChecks.checkNotEmpty(exprs);
    for (final Node expr : exprs) {
      InvariantChecks.checkNotNull(expr);
      if (!expr.isType(typeId)) {
        return false;
      }
    }
    return true;
  }

  /**
   * Checks whether all of the specified expressions have the specified type
   * (types are compared on the {@link DataType} level).
   *
   * @param type Expected data type.
   * @param exprs Expressions to be checked.
   * @return {@code true} if all expression types match the type specified by
   * the {@code type} argument or {@code false} otherwise.
   *
   * @throws IllegalArgumentException if the expression array is empty;
   *         if any expression in the array is {@code null}.
   */
  public static boolean isType(final DataType type, final Node... exprs) {
    InvariantChecks.checkNotEmpty(exprs);
    for (final Node expr : exprs) {
      InvariantChecks.checkNotNull(expr);
      if (!expr.isType(type)) {
        return false;
      }
    }
    return true;
  }

  /**
   * Checks whether all of the specified expressions are of the specified
   * kind (see {@link Node.Kind}).
   *
   * @param kind Expected expression kind.
   * @param exprs Expressions to be checked.
   * @return {@code true} if all expressions are of the specified kind or
   *         {@code false} otherwise.
   *
   * @throws IllegalArgumentException if the expression array is empty;
   *         if any expression in the array is {@code null}.
   */
  public static boolean isKind(final Node.Kind kind, final Node... exprs) {
    InvariantChecks.checkNotEmpty(exprs);
    for (final Node expr : exprs) {
      InvariantChecks.checkNotNull(expr);
      if (expr.getKind() != kind) {
        return false;
      }
    }
    return true;
  }

  /**
   * Checks whether the expression is represented by the specified operation.
   *
   * @param expr Expression to be checked.
   * @param opId Operation identifier.
   * @param <T> Operation identifier type.
   * @return {@code true} if the expression is represented by the specified operation
   *         or {@code false} otherwise.
   *
   * @throws IllegalArgumentException if any of the parameters is {@code null}.
   */
  public static <T extends Enum<? extends T>> boolean isOperation(final Node expr, final T opId) {
    InvariantChecks.checkNotNull(expr);
    InvariantChecks.checkNotNull(opId);
    return Node.Kind.OPERATION == expr.getKind() &&
           ((NodeOperation) expr).getOperationId() == opId;
  }

  /**
   * Checks whether the expression is represented by one of the specified operations.
   *
   * @param expr Expression to be checked.
   * @param opIds Collection of operation identifiers.
   * @param <T> Operation identifier type.
   * @return {@code true} if the expression is represented by one of the specified operations
   *         or {@code false} otherwise.
   *
   * @throws IllegalArgumentException if any of the parameters is {@code null};
   *         if the list of operation identifiers is empty.
   */
  public static <T extends Enum<? extends T>> boolean isOperation(final Node expr, final Collection<T> opIds) {
    InvariantChecks.checkNotNull(expr);
    InvariantChecks.checkNotEmpty(opIds);

    if (Node.Kind.OPERATION == expr.getKind()) {
      final Enum<?> exprOpId = ((NodeOperation) expr).getOperationId();
      for (final T opId : opIds) {
        if (exprOpId == opId) {
          return true;
        }
      }
    }

    return false;
  }

  /**
   * Checks whether the specified expression is represented by a constant value.
   *
   * @param expr Expression to be checked.
   * @return {@code true} if the expression is a value or {@code false} otherwise.
   *
   * @throws IllegalArgumentException if the parameter is {@code null}.
   */
  public static boolean isValue(final Node expr) {
    InvariantChecks.checkNotNull(expr);
    return Node.Kind.VALUE == expr.getKind();
  }

  /**
   * Checks whether the specified expression is represented by a variable.
   *
   * @param expr Expression to be checked.
   * @return {@code true} if the expression is a variable or {@code false} otherwise.
   *
   * @throws IllegalArgumentException if the parameter is {@code null}.
   */
  public static boolean isVariable(final Node expr) {
    InvariantChecks.checkNotNull(expr);
    return Node.Kind.VARIABLE == expr.getKind();
  }

  /**
   * Checks whether the specified expression is a logical expression (can be evaluated to boolean).
   *
   * @param expr Expression to be checked.
   * @return {@code true} if the expression is logical (can be evaluated to boolean) or
   *         {@code false} otherwise.
   *
   * @throws IllegalArgumentException if the parameter is {@code null}.
   */
  public static boolean isCondition(final Node expr) {
    InvariantChecks.checkNotNull(expr);
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
   * @throws IllegalArgumentException if the parameter is {@code null}.
   */
  public static boolean isAtomicCondition(final Node expr) {
    if (!isCondition(expr)) {
      return false;
    }

    final Set<StandardOperation> logicOperations =
        EnumSet.of(StandardOperation.AND, StandardOperation.OR, StandardOperation.NOT,
            StandardOperation.XOR, StandardOperation.IMPL);

    final ExprTreeVisitor visitor = new ExprTreeVisitorDefault() {
      @Override
      public void onOperationBegin(final NodeOperation node) {
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
   * @throws IllegalArgumentException if the parameter is {@code null}.
   */
  public static boolean hasBindings(final Node expr) {
    InvariantChecks.checkNotNull(expr);

    final ExprTreeVisitor visitor = new ExprTreeVisitorDefault() {
      @Override
      public void onBindingBegin(final NodeBinding node) {
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
   * @throws IllegalArgumentException if the parameter is {@code null}.
   */
  public static boolean isConstant(final Node expr) {
    InvariantChecks.checkNotNull(expr);

    final ExprTreeVisitor visitor = new ExprTreeVisitorDefault() {
      // Variables bound to constant values (a stack of scopes).
      private final Deque<Set<String>> knownVariables = new LinkedList<Set<String>>();

      @Override
      public void onVariable(final NodeVariable variable) {
        if (variable.getVariable().hasValue()) {
          return;
        }

        for (final Set<String> scope : knownVariables) {
          if (scope.contains(variable.getName())) {
            return;
          }
        }

        setStatus(Status.ABORT);
      }

      @Override
      public void onBindingBegin(final NodeBinding node) {
        knownVariables.push(new HashSet<String>());
      }

      @Override
      public void onBindingEnd(final NodeBinding node) {
        knownVariables.pop();
      }

      @Override
      public void onBoundVariableEnd(
          final NodeBinding node,
          final NodeVariable variable,
          final Node value) {
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
   * @throws IllegalArgumentException if any argument in the array is {@code null};
   *         if no arguments are provided; if an argument is not a logical expression.
   */
  public static Node getConjunction(final Node... exprs) {
    InvariantChecks.checkNotEmpty(exprs);
    checkAllConditions(exprs);

    if (exprs.length == 1) {
      return exprs[0];
    }

    return Nodes.AND(exprs);
  }

  /**
   * Performs logical disjunction {@code (exprs[0] || ... || exprs[n-1])} of the specified
   * expressions and returns the resulting expression.
   *
   * @param exprs Expressions to be combined.
   * @return A logical disjunction of the specified expressions.
   *
   * @throws IllegalArgumentException if any argument in the array is {@code null};
   *         if no arguments are provided; if an argument is not a logical expression.
   */
  public static Node getDisjunction(final Node... exprs) {
    InvariantChecks.checkNotEmpty(exprs);
    checkAllConditions(exprs);

    if (exprs.length == 1) {
      return exprs[0];
    }

    return Nodes.OR(exprs);
  }

  /**
   * Performs logical negation {@code (!getConjunction(exprs[0], ..., exprs[n-1]))} of the specified
   * expressions combined with conjunction and returns the resulting expression.
   *
   * @param exprs Expressions to be combined.
   * @return A logical negation of the specified expressions.
   *
   * @throws IllegalArgumentException if any argument in the array is {@code null}; if no arguments
   *         are provided; if an argument is not a logical expression.
   */
  public static Node getNegation(final Node... exprs) {
    return Nodes.NOT(getConjunction(exprs));
  }

  /**
   * Performs logical complement (negation) {@code !(getDisjunction(exprs[0], ..., exprs[n-1])} of
   * the specified expressions combined with disjunction and returns the resulting expression.
   *
   * @param exprs Expressions to be combined.
   * @return A logical complement of the specified expressions.
   *
   * @throws IllegalArgumentException if any argument in the array is {@code null}; if no arguments are
   *         provided; if an argument is not a logical expression.
   */
  public static Node getComplement(final Node... exprs) {
    return Nodes.NOT(getDisjunction(exprs));
  }

  /**
   * Checks whether the specified logical conditions are complete
   * {@code !(getComplement(exprs[0], ..., exprs[n-1]) is SAT)}. N.B. The method uses the default
   * constraint solver to perform the check.
   *
   * @param exprs Conditions (logical expressions) to be checked.
   * @return {@code true} if the conditions are complete or {@code false} otherwise.
   *
   * @throws IllegalArgumentException if any argument in the array is {@code null};
   *         if no arguments are provided; if an argument is not a logical expression.
   */
  public static boolean areComplete(final Node... exprs) {
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
   * @throws IllegalArgumentException if any argument in the array is {@code null}; if no arguments are
   *         provided; if an argument is not a logical expression.
   */
  public static boolean areCompatible(final Node... exprs) {
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
   * @throws IllegalArgumentException (1) if the parameter is {@code null}; (2) if the expression
   *         description contains errors that prevent the solver engine from solving it in
   *         a correct way; (3) if the solver is unable to solve a constraint based on the given
   *         expression due to limitations of its implementation.
   * @throws IllegalStateException if the solver engine returned results with an unknown status.
   */
  public static boolean isSAT(final Node expr) {
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
   * @throws IllegalArgumentException if the parameter is {@code null}.
   * @throws IllegalStateException if the method finds nodes that refer to different variables that
   *         have the same name.
   */
  public static Collection<NodeVariable> getVariables(final Node expr) {
    InvariantChecks.checkNotNull(expr);
    return getVariables(Collections.singletonList(expr));
  }

  /**
   * Returns all variables used in the specified expressions.
   *
   * @param exprs Collection of expressions to be processed.
   * @return A collection of all variables used in the specified expressions.
   *
   * @throws IllegalArgumentException if the parameter is {@code null}.
   * @throws IllegalStateException if the method finds nodes that refer to different
   *         variables that have the same name.
   */
  public static Collection<NodeVariable> getVariables(final Iterable<Node> exprs) {
    InvariantChecks.checkNotNull(exprs);

    final String ERR_MULTIPLE_VARS =
        "References to different variables that have the same name %s.";

    final Map<String, NodeVariable> variables = new HashMap<String, NodeVariable>();
    final ExprTreeWalker walker = new ExprTreeWalker(new ExprTreeVisitorDefault() {
      @Override
      public void onVariable(final NodeVariable variable) {
        InvariantChecks.checkNotNull(variable);
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

  private static void checkAllConditions(final Node... exprs) {
    for (final Node expr : exprs) {
      if (!isCondition(expr)) {
        throw new IllegalArgumentException("Expression is not a condition: " + expr.toString());
      }
    }
  }
}
