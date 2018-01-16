/*
 * Copyright 2017 ISP RAS (http://www.ispras.ru)
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

public class ConcatenationTestCase extends GenericSolverTestBase {
  public ConcatenationTestCase() {
    super(new Concatenation());
  }

  /**
   * The constraint as described in the SMT language:
   *
   * <pre>
   * (declare-const x (_ BitVec 16))
   * (declare-const y (_ BitVec 16))
   * (declare-const z (_ BitVec 32))
   * (assert (= x #x0000))
   * (assert (= y #xffff))
   * (assert (= z (concat x y)))
   * (check-sat)
   * (get-value (x y z))
   * (exit)
   * </pre>
   *
   * Expected output:
   *
   * <pre>
   * sat ((x #x0000) (y #xffff) (z #x0000ffff))
   * </pre>
   */
  public static class Concatenation implements SampleConstraint {
    private static final int BIT_VECTOR_ARG_SIZE = 16;
    private static final DataType BIT_VECTOR_ARG_TYPE = DataType.BIT_VECTOR(BIT_VECTOR_ARG_SIZE);
    private static final int BIT_VECTOR_RES_SIZE = 32;
    private static final DataType BIT_VECTOR_RES_TYPE = DataType.BIT_VECTOR(BIT_VECTOR_RES_SIZE);

    private static final int HEX_RADIX = 16;

    @Override
    public Constraint getConstraint() {
      final ConstraintBuilder builder = new ConstraintBuilder();

      builder.setName("Concatenation");
      builder.setKind(ConstraintKind.FORMULA_BASED);
      builder.setDescription("Concatenation constraint");

      final NodeVariable x = new NodeVariable(builder.addVariable("x", BIT_VECTOR_ARG_TYPE));
      final NodeVariable y = new NodeVariable(builder.addVariable("y", BIT_VECTOR_ARG_TYPE));
      final NodeVariable z = new NodeVariable(builder.addVariable("z", BIT_VECTOR_RES_TYPE));

      final Formulas formulas = new Formulas();
      builder.setInnerRep(formulas);

      formulas.add(Nodes.eq(x, new NodeValue(BIT_VECTOR_ARG_TYPE.valueOf("0000", HEX_RADIX))));
      formulas.add(Nodes.eq(y, new NodeValue(BIT_VECTOR_ARG_TYPE.valueOf("ffff", HEX_RADIX))));
      formulas.add(Nodes.eq(z, Nodes.BVCONCAT(x, y)));

      return builder.build();
    }

    @Override
    public Iterable<Variable> getExpectedVariables() {
      final List<Variable> result = new ArrayList<Variable>();

      result.add(new Variable("x", BIT_VECTOR_ARG_TYPE.valueOf("0000", HEX_RADIX)));
      result.add(new Variable("y", BIT_VECTOR_ARG_TYPE.valueOf("ffff", HEX_RADIX)));
      result.add(new Variable("z", BIT_VECTOR_RES_TYPE.valueOf("0000ffff", HEX_RADIX)));

      return result;
    }
  }
}
