/*
 * Copyright 2012-2017 ISP RAS (http://www.ispras.ru)
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

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.Nodes;

import java.util.ArrayList;
import java.util.List;

public class InputParametersTestCase extends GenericSolverTestBase {
  public InputParametersTestCase() {
    super(new InputParameters());
  }

  /**
   * The constraint as described in the SMT-LIB language:
   *
   * <pre>
   * (declare-const a (_ BitVec 16))
   * (declare-const b (_ BitVec 16))
   * (declare-const c (_ BitVec 16))
   *
   * (assert (= a #x0003)) ; assumed input value
   * (assert (= c #x0005)) ; assumed input value
   *
   * (assert (= (bvadd a b) c))
   *
   * (check-sat)
   * (get-value (a b c))
   * (exit)
   * </pre>
   * Expected output:
   *
   * <pre>
   * sat ((a #x0003)(b #x0002)(c #x0005))
   * </pre>
   */
  public static class InputParameters implements SampleConstraint {
    private static final int BIT_VECTOR_SIZE = 16;
    private static final DataType BIT_VECTOR_TYPE = DataType.BIT_VECTOR(BIT_VECTOR_SIZE);

    public Constraint getConstraint() {
      final ConstraintBuilder builder = new ConstraintBuilder();

      builder.setName("InputParameters");
      builder.setKind(ConstraintKind.FORMULA_BASED);
      builder.setDescription("InputParameters constraint");

      final NodeVariable a = new NodeVariable(builder.addVariable("a", BIT_VECTOR_TYPE));
      final NodeVariable b = new NodeVariable(builder.addVariable("b", BIT_VECTOR_TYPE));
      final NodeVariable c = new NodeVariable(builder.addVariable("c", BIT_VECTOR_TYPE));

      final Formulas formulas = new Formulas();
      builder.setInnerRep(formulas);

      formulas.add(Nodes.eq(Nodes.bvadd(a, b), c));

      final Constraint constraint = builder.build();

      constraint.setVariableValue("b", Data.newBitVector(2, 16));
      constraint.setVariableValue("c", Data.newBitVector(5, 16));

      return constraint;
    }

    public Iterable<Variable> getExpectedVariables() {
      final List<Variable> result = new ArrayList<Variable>();

      result.add(new Variable("a", BIT_VECTOR_TYPE.valueOf("3", 16)));

      return result;
    }
  }
}
