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

package ru.ispras.fortress.solver.constraint;

import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.Nodes;

import java.util.ArrayList;
import java.util.List;

public class ConstraintConjunctionTestCase extends GenericSolverTestBase {
  public ConstraintConjunctionTestCase() {
    super(new ConstraintConjunction());
  }

  public static class ConstraintConjunction extends BVUGTOperation {
    @Override
    public Constraint getConstraint() {
      final Constraint constraint = super.getConstraint();
      final Constraint neg = ConstraintCombiner.makeNegation(constraint);
      final Constraint conjunction = ConstraintCombiner.makeConjunction(constraint, neg);

      final ConstraintBuilder builder = new ConstraintBuilder();

      builder.setKind(constraint.getKind());
      builder.setName(conjunction.getName());

      for (final Variable var : conjunction.getVariables()) {
        builder.addVariable(var.getName(), var.getData());
      }

      final Formulas formulas = new Formulas();
      builder.setInnerRep(formulas);

      formulas.add(Nodes.NOT(Nodes.AND(
          ((Formulas) conjunction.getInnerRep()).exprs().iterator().next(),
          ((Formulas) conjunction.getInnerRep()).exprs().iterator().next())));

      return builder.build();
    }

    @Override
    public Iterable<Variable> getExpectedVariables() {
      final List<Variable> result = new ArrayList<Variable>();
      result.add(new Variable("x", BIT_VECTOR_TYPE.valueOf("0", 10)));
      return result;
    }
  }
}
