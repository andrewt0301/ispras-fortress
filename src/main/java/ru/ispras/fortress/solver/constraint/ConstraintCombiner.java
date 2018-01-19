/*
 * Copyright 2013-2017 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.solver.constraint;

import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.Nodes;
import ru.ispras.fortress.util.InvariantChecks;

/**
 * The {@link ConstraintCombiner} class provides methods to create new constraints by combining
 * existing ones (by performing negation, logical conjunction and logical disjunction).
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public final class ConstraintCombiner {
  private static final String DISJUNCTION = "Disjunction_of_%s_and_%s";
  private static final String CONJUNCTION = "Conjunction_of_%s_and_%s";
  private static final String NEGATION = "Negation_of_%s";

  private ConstraintCombiner() {}

  /**
   * Creates a new constraint by performing logical negation on the specified constraint.
   *
   * @param constraint A constraint object.
   * @return A new constraint object.
   *
   * @throws IllegalArgumentException if the parameter equals {@code null};
   *         if the parameter is not a formula-based constraint (its type
   *         is not ConstraintKind.FORMULA_BASED).
   */
  public static Constraint makeNegation(final Constraint constraint) {
    formulaBasedCheck(constraint);

    final ConstraintBuilder builder = new ConstraintBuilder(constraint.getKind());

    final String name = String.format(NEGATION, constraint.getName());
    builder.setName(name);

    final Formulas formulas = new Formulas();
    builder.setInnerRep(formulas);

    final Node sourceExpr = ((Formulas) constraint.getInnerRep()).asSingleExpr();
    formulas.add(Nodes.not(sourceExpr));

    builder.addVariableCopies(constraint.getVariables());
    return builder.build();
  }

  /**
   * Creates a new constraint by performing logical conjunction on the specified constraints.
   *
   * @param first A constraint object.
   * @param second A constraint object.
   * @return A new constraint object.
   *
   * @throws IllegalArgumentException if any of the parameters equals {@code null};
   *         if any of the parameters is not a formula-based constraint
   *         (its type is not ConstraintKind.FORMULA_BASED).
   */
  public static Constraint makeConjunction(final Constraint first, final Constraint second) {
    formulaBasedCheck(first);
    formulaBasedCheck(second);

    final ConstraintBuilder builder = new ConstraintBuilder(first.getKind());

    final String name = String.format(CONJUNCTION, first.getName(), second.getName());
    builder.setName(name);

    final Formulas formulas = new Formulas();
    builder.setInnerRep(formulas);

    formulas.addAll((Formulas) first.getInnerRep());
    formulas.addAll((Formulas) second.getInnerRep());

    builder.addVariableCopies(first.getVariables());
    builder.addVariableCopies(second.getVariables());

    return builder.build();
  }

  /**
   * Creates a new constraint by performing logical disjunction on the specified constraints.
   *
   * @param first A constraint object.
   * @param second A constraint object.
   * @return A new constraint object.
   *
   * @throws IllegalArgumentException if any of the parameters equals {@code null};
   *         if any of the parameters is not a formula-based constraint
   *         (its type is not ConstraintKind.FORMULA_BASED).
   */
  public static Constraint makeDisjunction(final Constraint first, final Constraint second) {
    formulaBasedCheck(first);
    formulaBasedCheck(second);

    final ConstraintBuilder builder = new ConstraintBuilder(first.getKind());

    final String name = String.format(DISJUNCTION, first.getName(), second.getName());
    builder.setName(name);

    final Formulas formulas = new Formulas();
    builder.setInnerRep(formulas);

    final Node sourceExprA = ((Formulas) first.getInnerRep()).asSingleExpr();
    final Node sourceExprB = ((Formulas) second.getInnerRep()).asSingleExpr();
    formulas.add(Nodes.or(sourceExprA, sourceExprB));

    builder.addVariableCopies(first.getVariables());
    builder.addVariableCopies(second.getVariables());

    return builder.build();
  }

  private static void formulaBasedCheck(final Constraint constraint) {
    InvariantChecks.checkNotNull(constraint);
    if (ConstraintKind.FORMULA_BASED != constraint.getKind()) {
      throw new IllegalArgumentException(String.format(
          "The %s constraint is not formula based.", constraint.getName()));
    }
  }
}
