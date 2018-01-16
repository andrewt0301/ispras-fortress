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
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.Nodes;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintBuilder;
import ru.ispras.fortress.solver.constraint.ConstraintKind;
import ru.ispras.fortress.solver.constraint.Formulas;
import ru.ispras.fortress.solver.constraint.GenericSolverTestBase;

import java.util.Arrays;

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
    private static final DataType bitVector6 = DataType.BIT_VECTOR(6);

    private static final NodeValue boolTrue = NodeValue.newBoolean(true);
    private static final NodeValue int2 = NodeValue.newInteger(2);
    private static final NodeValue int7 = NodeValue.newInteger(7);
    private static final NodeValue bv1 = NodeValue.newBitVector(BitVector.valueOf("1", 2, 1));
    private static final NodeValue bv3 = NodeValue.newBitVector(BitVector.valueOf("11", 2, 2));
    private static final NodeValue bv7 = NodeValue.newBitVector(BitVector.valueOf("111", 2, 3));
    private static final NodeValue bv63 = NodeValue.newBitVector(BitVector.valueOf("111111", 2, 6));

    @Override
    public Constraint getConstraint() {
      final ConstraintBuilder builder = new ConstraintBuilder();

      builder.setName("ConstCast");
      builder.setKind(ConstraintKind.FORMULA_BASED);
      builder.setDescription("ConstCast constraint");

      final NodeVariable x = new NodeVariable(builder.addVariable("x", intType));
      final NodeVariable y = new NodeVariable(builder.addVariable("y", intType));
      final NodeVariable z = new NodeVariable(builder.addVariable("z", intType));
      final NodeVariable w = new NodeVariable(builder.addVariable("w", bitVector3));
      final NodeVariable v = new NodeVariable(builder.addVariable("v", boolType));
      final NodeVariable u = new NodeVariable(builder.addVariable("u", intType));
      final NodeVariable t = new NodeVariable(builder.addVariable("t", bitVector6));
      final NodeVariable s = new NodeVariable(builder.addVariable("s", intType));
      final NodeVariable r = new NodeVariable(builder.addVariable("r", bitVector3));
      final NodeVariable p = new NodeVariable(builder.addVariable("p", bitVector3));

      final Formulas formulas = new Formulas();
      builder.setInnerRep(formulas);

      formulas.add(TypeConversion.castConstants(Nodes.eq( x, bv7)));
      formulas.add(TypeConversion.castConstants(Nodes.eq(Nodes.rem(y, bv3), z)));
      formulas.add(TypeConversion.castConstants(Nodes.eq(bv7, Nodes.bvadd(w, int2))));
      formulas.add(TypeConversion.castConstants(Nodes.and(v, int2)));
      formulas.add(TypeConversion.castConstants(Nodes.less(u, bv3)));
      formulas.add(TypeConversion.castConstants(Nodes.eq(Nodes.BVEXTRACT(bv3, int2, t), boolTrue)));
      formulas.add(TypeConversion.castConstants(Nodes.eq( int2, Nodes.ite(bv3, s, u))));
      formulas.add(TypeConversion.castConstants(Nodes.eq(bv63, Nodes.bvrepeat(bv1, r))));
      formulas.add(TypeConversion.castConstants(Nodes.eq(bv63, Nodes.bvconcat(p, int7))));

      return builder.build();
    }

    @Override
    public Iterable<Variable> getExpectedVariables() {

      return Arrays.asList(
          new Variable("x", intType.valueOf("7", 10)),
          new Variable("y", intType.valueOf("0", 10)),
          new Variable("z", intType.valueOf("0", 10)),
          new Variable("w", bitVector3.valueOf("101", 2)),
          new Variable("v", boolType.valueOf("1", 2)),
          new Variable("u", intType.valueOf("0", 10)),
          new Variable("t", bitVector6.valueOf("001100", 2)),
          new Variable("s", intType.valueOf("2", 10)),
          new Variable("r", bitVector3.valueOf("111", 2)),
          new Variable("p", bitVector3.valueOf("111", 2)));
    }
  }
}
