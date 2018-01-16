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

package ru.ispras.fortress.solver.constraint;

import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.Nodes;

import java.util.ArrayList;
import java.util.List;

public class ConstraintNegationTestCase extends GenericSolverTestBase {
  public ConstraintNegationTestCase() {
    super(new ConstraintNegation());
  }

  public static class ConstraintNegation extends BVUGTOperation {
    public Constraint getConstraint() {
      final Constraint constraint = super.getConstraint();
      final Node formula = ((Formulas) constraint.getInnerRep()).exprs().iterator().next();

      final Constraint neg = ConstraintCombiner.makeNegation(constraint);
      final Node negFormula = ((Formulas) neg.getInnerRep()).exprs().iterator().next();

      final ConstraintBuilder builder = new ConstraintBuilder();

      builder.setName("ConstraintNegation");
      builder.setKind(constraint.getKind());

      for (final Variable var : constraint.getVariables()) {
        builder.addVariable(var.getName(), var.getData());
      }

      final Formulas formulas = new Formulas();
      builder.setInnerRep(formulas);

      // not(= (a not(not(a))))
      formulas.add(Nodes.not(Nodes.eq(formula, Nodes.not(negFormula))));

      // (not(a) and a)
      formulas.add(Nodes.and(negFormula, formula));

      // not((not(a)) or a)
      formulas.add(Nodes.not(Nodes.or(negFormula, formula)));

      return ConstraintCombiner.makeNegation(builder.build());
    }

    @Override
    public Iterable<Variable> getExpectedVariables() {
      final List<Variable> result = new ArrayList<Variable>();

      result.add(new Variable("x", BIT_VECTOR_TYPE.valueOf("0", 10)));

      return result;
    }
  }
}
