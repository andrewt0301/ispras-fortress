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

import org.junit.Assert;

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.Nodes;

import java.util.Arrays;

/**
 * The constraint as described in the SMT-LIB language:
 *
 * <pre>
 * (declare-const x (_ BitVec 32))
 * (declare-const y (_ BitVec 8))
 * (assert (= x (_ bv257 32)))
 * (assert (= y ((_ extract 7 0) x)))
 * (check-sat)
 * (get-value (x y))
 * (exit)
 * </pre>
 * Expected output:
 *
 * <pre>
 * sat ((x #x00000101) (y #x01))
 * </pre>
 */
public class BitVectorExtractionTestCase extends GenericSolverTestBase {
  public BitVectorExtractionTestCase() {
    super(new BitVectorExtractionConstraint());
  }

  public static final class BitVectorExtractionConstraint implements SampleConstraint {
    private static final DataType BitVector32 = DataType.BIT_VECTOR(32);
    private static final DataType BitVector8 = DataType.BIT_VECTOR(8);

    public Constraint getConstraint() {
      final ConstraintBuilder builder = new ConstraintBuilder();

      builder.setName("BVEXTRACT");
      builder.setKind(ConstraintKind.FORMULA_BASED);
      builder.setDescription("Bitvector extraction constraint");

      final NodeVariable x = new NodeVariable(builder.addVariable("x", BitVector32));
      final NodeVariable y = new NodeVariable(builder.addVariable("y", BitVector8));

      final Formulas formulas = new Formulas();
      builder.setInnerRep(formulas);

      formulas.add(Nodes.eq(x, new NodeValue(BitVector32.valueOf("257", 10))));

      final Node extraction = Nodes.bvextract(7, 0, x);
      Assert.assertEquals(DataType.BIT_VECTOR(8), extraction.getDataType());

      formulas.add(Nodes.eq(y, extraction));

      return builder.build();
    }

    public Iterable<Variable> getExpectedVariables() {
      return Arrays.asList(
          new Variable("x", BitVector32.valueOf("257", 10)),
          new Variable("y", BitVector8.valueOf("1", 10)));
    }
  }
}
