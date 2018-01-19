/*
 * Copyright 2017-2018 ISP RAS (http://www.ispras.ru)
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

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.Nodes;

import java.util.ArrayList;
import java.util.List;

/**
 * This test constructs a constraint, solves it and checks the solution against the expected output.
 * The constraint as described in the SMT language:
 *
 * <pre>
 * (declare-const x (_ BitVec 32))
 * (declare-const y Int)
 * (assert (= y 129))
 * (assert (= (bv2int x) y))
 * (check-sat)
 * (get-model)
 * (get-value (x y))
 * (exit)
 * </pre>
 * Expected output: sat ((x #x00000081) (y 129))
 */
public class BvToIntTestCase extends GenericSolverTestBase {
  public BvToIntTestCase() {
    super(new BvToIntOperation());
  }

  public static class BvToIntOperation implements SampleConstraint {
    private static final DataType INT_TYPE = DataType.INTEGER;
    private static final int BIT_VECTOR_SIZE = 32;
    private static final DataType BIT_VECTOR_TYPE = DataType.BIT_VECTOR(BIT_VECTOR_SIZE);

    @Override
    public Constraint getConstraint() {
      final ConstraintBuilder builder = new ConstraintBuilder();

      builder.setName("BvToInt");
      builder.setKind(ConstraintKind.FORMULA_BASED);
      builder.setDescription("BvToInt constraint");

      final NodeVariable x = new NodeVariable(builder.addVariable("x", BIT_VECTOR_TYPE));
      final NodeVariable y = new NodeVariable(builder.addVariable("y", INT_TYPE));

      final Formulas formulas = new Formulas();
      builder.setInnerRep(formulas);

      formulas.add(Nodes.eq(y, NodeValue.newInteger(129)));
      formulas.add(Nodes.eq(y, Nodes.bv2int(x)));

      return builder.build();
    }

    @Override
    public Iterable<Variable> getExpectedVariables() {
      final List<Variable> result = new ArrayList<>();

      result.add(new Variable("x", BIT_VECTOR_TYPE.valueOf("81", 16)));
      result.add(new Variable("y", INT_TYPE.valueOf("129", 10)));

      return result;
    }
  }
}
