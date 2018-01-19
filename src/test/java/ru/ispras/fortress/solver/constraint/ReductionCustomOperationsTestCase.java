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

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.Nodes;

import java.util.Arrays;

public class ReductionCustomOperationsTestCase extends GenericSolverTestBase {
  public ReductionCustomOperationsTestCase() {
    super(new ReductionCustomOperations());
  }

  public static class ReductionCustomOperations implements SampleConstraint {
    // Data Types and Constants
    private static final int BIT_VECTOR_SIZE = 8;
    private static final DataType BIT_VECTOR_TYPE = DataType.bitVector(BIT_VECTOR_SIZE);

    private static final int BIT_BOOL_SIZE = 1;
    private static final DataType BIT_BOOL_TYPE = DataType.bitVector(BIT_BOOL_SIZE);

    private static final Data BIT_TRUE = Data.newBitVector(1, BIT_BOOL_SIZE);
    private static final Data BIT_FALSE = Data.newBitVector(0, BIT_BOOL_SIZE);

    // Test Data Constants
    private static final Node NO_BITS = new NodeValue(BIT_VECTOR_TYPE.valueOf("00000000", 2));
    private static final Node ALL_BITS = new NodeValue(BIT_VECTOR_TYPE.valueOf("11111111", 2));
    private static final Node EVEN_BITS = new NodeValue(BIT_VECTOR_TYPE.valueOf("00111100", 2));
    private static final Node ODD_BITS = new NodeValue(BIT_VECTOR_TYPE.valueOf("10000000", 2));

    @Override
    public Constraint getConstraint() {
      final ConstraintBuilder builder = new ConstraintBuilder();

      builder.setName("ReductionCustomOperations");
      builder.setKind(ConstraintKind.FORMULA_BASED);
      builder.setDescription("Constraint to test reduction operations (Verilog-like).");

      final NodeVariable bvandrNoBits =
          new NodeVariable(builder.addVariable("bvandrNoBits", BIT_BOOL_TYPE));
      final NodeVariable bvandrAllBits =
          new NodeVariable(builder.addVariable("bvandrAllBits", BIT_BOOL_TYPE));
      final NodeVariable bvandrEvenBits =
          new NodeVariable(builder.addVariable("bvandrEvenBits", BIT_BOOL_TYPE));
      final NodeVariable bvandrOddBits =
          new NodeVariable(builder.addVariable("bvandrOddBits", BIT_BOOL_TYPE));

      final NodeVariable bvnandrNoBits =
          new NodeVariable(builder.addVariable("bvnandrNoBits", BIT_BOOL_TYPE));
      final NodeVariable bvnandrAllBits =
          new NodeVariable(builder.addVariable("bvnandrAllBits", BIT_BOOL_TYPE));
      final NodeVariable bvnandrEvenBits =
          new NodeVariable(builder.addVariable("bvnandrEvenBits", BIT_BOOL_TYPE));
      final NodeVariable bvnandrOddBits =
          new NodeVariable(builder.addVariable("bvnandrOddBits", BIT_BOOL_TYPE));

      final NodeVariable bvorrNoBits =
          new NodeVariable(builder.addVariable("bvorrNoBits", BIT_BOOL_TYPE));
      final NodeVariable bvorrAllBits =
          new NodeVariable(builder.addVariable("bvorrAllBits", BIT_BOOL_TYPE));
      final NodeVariable bvorrEvenBits =
          new NodeVariable(builder.addVariable("bvorrEvenBits", BIT_BOOL_TYPE));
      final NodeVariable bvorrOddBits =
          new NodeVariable(builder.addVariable("bvorrOddBits", BIT_BOOL_TYPE));

      final NodeVariable bvnorrNoBits =
          new NodeVariable(builder.addVariable("bvnorrNoBits", BIT_BOOL_TYPE));
      final NodeVariable bvnorrAllBits =
          new NodeVariable(builder.addVariable("bvnorrAllBits", BIT_BOOL_TYPE));
      final NodeVariable bvnorrEvenBits =
          new NodeVariable(builder.addVariable("bvnorrEvenBits", BIT_BOOL_TYPE));
      final NodeVariable bvnorrOddBits =
          new NodeVariable(builder.addVariable("bvnorrOddBits", BIT_BOOL_TYPE));

      final NodeVariable bvxorrNoBits =
          new NodeVariable(builder.addVariable("bvxorrNoBits", BIT_BOOL_TYPE));
      final NodeVariable bvxorrAllBits =
          new NodeVariable(builder.addVariable("bvxorrAllBits", BIT_BOOL_TYPE));
      final NodeVariable bvxorrEvenBits =
          new NodeVariable(builder.addVariable("bvxorrEvenBits", BIT_BOOL_TYPE));
      final NodeVariable bvxorrOddBits =
          new NodeVariable(builder.addVariable("bvxorrOddBits", BIT_BOOL_TYPE));

      final NodeVariable bvxnorrNoBits =
          new NodeVariable(builder.addVariable("bvxnorrNoBits", BIT_BOOL_TYPE));
      final NodeVariable bvxnorrAllBits =
          new NodeVariable(builder.addVariable("bvxnorrAllBits", BIT_BOOL_TYPE));
      final NodeVariable bvxnorrEvenBits =
          new NodeVariable(builder.addVariable("bvxnorrEvenBits", BIT_BOOL_TYPE));
      final NodeVariable bvxnorrOddBits =
          new NodeVariable(builder.addVariable("bvxnorrOddBits", BIT_BOOL_TYPE));

      final Formulas formulas = new Formulas();
      builder.setInnerRep(formulas);

      // BVANDR Asserts
      formulas.add(Nodes.eq(bvandrNoBits,   Nodes.bvandr(NO_BITS)));
      formulas.add(Nodes.eq(bvandrAllBits,  Nodes.bvandr(ALL_BITS)));
      formulas.add(Nodes.eq(bvandrEvenBits, Nodes.bvandr(EVEN_BITS)));
      formulas.add(Nodes.eq(bvandrOddBits,  Nodes.bvandr(ODD_BITS)));

      // BVNANDR Asserts
      formulas.add(Nodes.eq(bvnandrNoBits,   Nodes.bvnandr(NO_BITS)));
      formulas.add(Nodes.eq(bvnandrAllBits,  Nodes.bvnandr(ALL_BITS)));
      formulas.add(Nodes.eq(bvnandrEvenBits, Nodes.bvnandr(EVEN_BITS)));
      formulas.add(Nodes.eq(bvnandrOddBits,  Nodes.bvnandr(ODD_BITS)));

      // BVORR Asserts
      formulas.add(Nodes.eq(bvorrNoBits,   Nodes.bvorr(NO_BITS)));
      formulas.add(Nodes.eq(bvorrAllBits,  Nodes.bvorr(ALL_BITS)));
      formulas.add(Nodes.eq(bvorrEvenBits, Nodes.bvorr(EVEN_BITS)));
      formulas.add(Nodes.eq(bvorrOddBits,  Nodes.bvorr(ODD_BITS)));

      // BVNORR Asserts
      formulas.add(Nodes.eq(bvnorrNoBits,   Nodes.bvnorr(NO_BITS)));
      formulas.add(Nodes.eq(bvnorrAllBits,  Nodes.bvnorr(ALL_BITS)));
      formulas.add(Nodes.eq(bvnorrEvenBits, Nodes.bvnorr(EVEN_BITS)));
      formulas.add(Nodes.eq(bvnorrOddBits,  Nodes.bvnorr(ODD_BITS)));

      // BVXORR Asserts
      formulas.add(Nodes.eq(bvxorrNoBits,   Nodes.bvxorr(NO_BITS)));
      formulas.add(Nodes.eq(bvxorrAllBits,  Nodes.bvxorr(ALL_BITS)));
      formulas.add(Nodes.eq(bvxorrEvenBits, Nodes.bvxorr(EVEN_BITS)));
      formulas.add(Nodes.eq(bvxorrOddBits,  Nodes.bvxorr(ODD_BITS)));

      // BVXNORR Asserts

      formulas.add(Nodes.eq(bvxnorrNoBits,   Nodes.bvxnorr(NO_BITS)));
      formulas.add(Nodes.eq(bvxnorrAllBits,  Nodes.bvxnorr(ALL_BITS)));
      formulas.add(Nodes.eq(bvxnorrEvenBits, Nodes.bvxnorr(EVEN_BITS)));
      formulas.add(Nodes.eq(bvxnorrOddBits,  Nodes.bvxnorr(ODD_BITS)));

      return builder.build();
    }

    @Override
    public Iterable<Variable> getExpectedVariables() {
      return Arrays.asList(new Variable("bvandrNoBits", BIT_FALSE), new Variable(
          "bvandrAllBits", BIT_TRUE), new Variable("bvandrEvenBits", BIT_FALSE),
          new Variable("bvandrOddBits", BIT_FALSE),

          new Variable("bvnandrNoBits", BIT_TRUE), new Variable("bvnandrAllBits",
              BIT_FALSE), new Variable("bvnandrEvenBits", BIT_TRUE), new Variable(
              "bvnandrOddBits", BIT_TRUE),

          new Variable("bvorrNoBits", BIT_FALSE), new Variable("bvorrAllBits", BIT_TRUE),
          new Variable("bvorrEvenBits", BIT_TRUE),
          new Variable("bvorrOddBits", BIT_TRUE),

          new Variable("bvnorrNoBits", BIT_TRUE),
          new Variable("bvnorrAllBits", BIT_FALSE), new Variable("bvnorrEvenBits",
              BIT_FALSE), new Variable("bvnorrOddBits", BIT_FALSE),

          new Variable("bvxorrNoBits", BIT_FALSE), new Variable("bvxorrAllBits",
              BIT_FALSE), new Variable("bvxorrEvenBits", BIT_FALSE), new Variable(
              "bvxorrOddBits", BIT_TRUE),

          new Variable("bvxnorrNoBits", BIT_TRUE), new Variable("bvxnorrAllBits",
              BIT_TRUE), new Variable("bvxnorrEvenBits", BIT_TRUE), new Variable(
              "bvxnorrOddBits", BIT_FALSE));
    }
  }
}
