/*
 * Copyright 2014-2018 ISP RAS (http://www.ispras.ru)
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
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.Nodes;

import java.util.Arrays;

/**
 * The constraint as described in the SMT-LIB language:
 *
 * <pre>
 * (declare-const x (_ BitVec 32))
 * (declare-const y (_ BitVec 1))
 * (assert (= y ((_ extract 0 0) x))
 * (check-sat)
 * (get-value (x y))
 * (exit)
 * </pre>
 * Expected output:
 *
 * <pre>
 * sat ((x #x00000000) (y #b0))
 * </pre>
 */
public class BitVectorLiteralTestCase extends GenericSolverTestBase {
  public BitVectorLiteralTestCase() {
    super(new BitVectorLiteralConstraint());
  }

  public static final class BitVectorLiteralConstraint implements SampleConstraint {
    private static final DataType BitVector32 = DataType.BIT_VECTOR(32);
    private static final DataType BitVector1 = DataType.BIT_VECTOR(1);

    public Constraint getConstraint() {
      final ConstraintBuilder builder = new ConstraintBuilder();

      builder.setName("BitVectorLiteral");
      builder.setKind(ConstraintKind.FORMULA_BASED);
      builder.setDescription("BitVector solving with different literal radix in output");

      final NodeVariable x = new NodeVariable(builder.addVariable("x", BitVector32));
      final NodeVariable y = new NodeVariable(builder.addVariable("y", BitVector1));

      final Formulas formulas = new Formulas();
      builder.setInnerRep(formulas);

      final Node bit = Nodes.bvextract(0, 0, x);
      formulas.add(Nodes.eq(y, bit));

      return builder.build();
    }

    public Iterable<Variable> getExpectedVariables() {
      return Arrays.asList(
          new Variable("x", BitVector32.valueOf("0", 10)),
          new Variable("y", BitVector1.valueOf("0", 10)));
    }
  }
}
