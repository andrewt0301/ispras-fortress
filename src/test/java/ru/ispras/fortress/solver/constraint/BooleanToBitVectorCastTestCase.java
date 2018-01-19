/*
 * Copyright 2014-2018 ISP RAS (http://www.ispras.ru)
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package ru.ispras.fortress.solver.constraint;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.data.types.bitvector.BitVector;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.Nodes;

import java.util.ArrayList;
import java.util.List;

/**
 * Test for boolean expressions casting into bit vectors with size 1.
 * Such cast is needed when the code of corresponding operation is of bit vector family.
 *
 * @author <a href="mailto:smolov@ispras.ru">Sergey Smolov</a>
 */
public class BooleanToBitVectorCastTestCase extends GenericSolverTestBase {

  public BooleanToBitVectorCastTestCase() {
    super(new BooleanToBitVectorCast());
  }

  /**
   * This class constructs a constraint and provides expected output.
   * The following SMT-LIB code is incorrect:
   * <pre>
   * (declare-const x Int)
   * (declare-const y Int)
   * (declare-const z (_ BitVec 1))
   * (assert (< x 2))
   * (assert (> y 0))
   * (assert (bvor (= x y) z))
   * (check-sat)
   * (get-value (x y z))
   * (exit)
   * </pre>
   * and produces an error (Z3 v 3.1):
   * (error "line 6 column 23: operator is applied to arguments of the wrong sort")
   *
   * <p>The library converts this into correct one:
   * <pre>
   * (declare-const x Int)
   * (declare-const y Int)
   * (declare-const z (_ BitVec 1))
   * (assert  (< x 2))
   * (assert  (> y 0))
   * (assert  (= (bvor (ite (= x y) #b1 #b0) z) #b1))
   * (check-sat)
   * (get-value ( x y z))
   * (get-model)
   * (exit)
   * </pre>
   */
  public static class BooleanToBitVectorCast implements SampleConstraint {
    @Override
    public Constraint getConstraint() {
      final ConstraintBuilder builder = new ConstraintBuilder();

      builder.setName("BooleanToBitVectorCast");
      builder.setKind(ConstraintKind.FORMULA_BASED);
      builder.setDescription("BooleanToBitVectorCast constraint");

      final NodeVariable x = new NodeVariable(builder.addVariable("x", DataType.INTEGER));
      final NodeVariable y = new NodeVariable(builder.addVariable("y", DataType.INTEGER));
      final NodeVariable z = new NodeVariable(builder.addVariable("z", DataType.bitVector(1)));

      final Formulas formulas = new Formulas();
      builder.setInnerRep(formulas);

      formulas.add(Nodes.less(x, NodeValue.newInteger(2)));
      formulas.add(Nodes.greater(y, NodeValue.newInteger(0)));

      formulas.add(Nodes.eq(
          Nodes.bvor(Nodes.bool2bv(Nodes.eq(x, y)), z),
          NodeValue.newBitVector(BitVector.valueOf(true))));

      return builder.build();
    }

    @Override
    public Iterable<Variable> getExpectedVariables() {
      final List<Variable> result = new ArrayList<>();

      result.add(new Variable("x", Data.newInteger(1)));
      result.add(new Variable("y", Data.newInteger(1)));
      result.add(new Variable("z", Data.newBitVector(0, 1)));

      return result;
    }
  }
}
