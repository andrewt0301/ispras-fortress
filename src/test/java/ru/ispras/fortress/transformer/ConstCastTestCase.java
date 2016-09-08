/*
 * Copyright 2016 ISP RAS (http://www.ispras.ru), UniTESK Lab (http://www.unitesk.com)
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package ru.ispras.fortress.transformer;

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.data.types.bitvector.BitVector;
import ru.ispras.fortress.expression.ExprUtils;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintBuilder;
import ru.ispras.fortress.solver.constraint.ConstraintKind;
import ru.ispras.fortress.solver.constraint.Formulas;
import ru.ispras.fortress.solver.constraint.GenericSolverTestBase;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * Constant casting methods test case.
 * @author <a href="mailto:smolov@ispras.ru">Sergey Smolov</a>
 */
public class ConstCastTestCase extends GenericSolverTestBase {

  public ConstCastTestCase() {
    super(new ConstCast());
  }

  public static class ConstCast implements SampleConstraint {

    private static final DataType intType = DataType.INTEGER;
    private static final DataType boolType = DataType.BOOLEAN;
    private static final DataType bitVector3 = DataType.BIT_VECTOR(3);

    private static final NodeValue bv3 = NodeValue.newBitVector(BitVector.valueOf("11", 2, 2));
    private static final NodeValue bv7 = NodeValue.newBitVector(BitVector.valueOf("111", 2, 3));

    @Override
    public Constraint getConstraint() {

      final ConstraintBuilder builder = new ConstraintBuilder();

      builder.setName("ConstCast");
      builder.setKind(ConstraintKind.FORMULA_BASED);
      builder.setDescription("ConstCast constraint");

      final NodeVariable x = new NodeVariable(builder.addVariable("x", intType));

      final NodeVariable y = new NodeVariable(builder.addVariable("y", intType));
      final NodeVariable z = new NodeVariable(builder.addVariable("z", intType));

      final Formulas formulas = new Formulas();
      builder.setInnerRep(formulas);

      formulas.add(castConstants(new NodeOperation(StandardOperation.EQ, x, bv7)));
      formulas.add(
          castConstants(
              new NodeOperation(
                  StandardOperation.EQ,
                  new NodeOperation(StandardOperation.POWER, y, bv3), z)));

      return builder.build();
    }

    @Override
    public Iterable<Variable> getExpectedVariables() {

      final List<Variable> result = new ArrayList<>();
      result.add(new Variable("x", intType.valueOf("7", 10)));
      result.add(new Variable("y", intType.valueOf("0", 10)));
      result.add(new Variable("z", intType.valueOf("0", 10)));
      return result;
    }
  }

  private static Node castConstants(final Node node) {
    final Collection<Node> casted = TypeConversion.castConstants(node, null);
    return ExprUtils.getConjunction(casted.toArray(new Node[casted.size()]));
  }
}
