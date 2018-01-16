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
    private static final DataType BIT_VECTOR_TYPE = DataType.BIT_VECTOR(BIT_VECTOR_SIZE);

    private static final int BIT_BOOL_SIZE = 1;
    private static final DataType BIT_BOOL_TYPE = DataType.BIT_VECTOR(BIT_BOOL_SIZE);

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

      final NodeVariable varBVANDR_NO_BITS =
          new NodeVariable(builder.addVariable("varBVANDR_NO_BITS", BIT_BOOL_TYPE));
      final NodeVariable varBVANDR_ALL_BITS =
          new NodeVariable(builder.addVariable("varBVANDR_ALL_BITS", BIT_BOOL_TYPE));
      final NodeVariable varBVANDR_EVEN_BITS =
          new NodeVariable(builder.addVariable("varBVANDR_EVEN_BITS", BIT_BOOL_TYPE));
      final NodeVariable varBVANDR_ODD_BITS =
          new NodeVariable(builder.addVariable("varBVANDR_ODD_BITS", BIT_BOOL_TYPE));

      final NodeVariable varBVNANDR_NO_BITS =
          new NodeVariable(builder.addVariable("varBVNANDR_NO_BITS", BIT_BOOL_TYPE));
      final NodeVariable varBVNANDR_ALL_BITS =
          new NodeVariable(builder.addVariable("varBVNANDR_ALL_BITS", BIT_BOOL_TYPE));
      final NodeVariable varBVNANDR_EVEN_BITS =
          new NodeVariable(builder.addVariable("varBVNANDR_EVEN_BITS", BIT_BOOL_TYPE));
      final NodeVariable varBVNANDR_ODD_BITS =
          new NodeVariable(builder.addVariable("varBVNANDR_ODD_BITS", BIT_BOOL_TYPE));

      final NodeVariable varBVORR_NO_BITS =
          new NodeVariable(builder.addVariable("varBVORR_NO_BITS", BIT_BOOL_TYPE));
      final NodeVariable varBVORR_ALL_BITS =
          new NodeVariable(builder.addVariable("varBVORR_ALL_BITS", BIT_BOOL_TYPE));
      final NodeVariable varBVORR_EVEN_BITS =
          new NodeVariable(builder.addVariable("varBVORR_EVEN_BITS", BIT_BOOL_TYPE));
      final NodeVariable varBVORR_ODD_BITS =
          new NodeVariable(builder.addVariable("varBVORR_ODD_BITS", BIT_BOOL_TYPE));

      final NodeVariable varBVNORR_NO_BITS =
          new NodeVariable(builder.addVariable("varBVNORR_NO_BITS", BIT_BOOL_TYPE));
      final NodeVariable varBVNORR_ALL_BITS =
          new NodeVariable(builder.addVariable("varBVNORR_ALL_BITS", BIT_BOOL_TYPE));
      final NodeVariable varBVNORR_EVEN_BITS =
          new NodeVariable(builder.addVariable("varBVNORR_EVEN_BITS", BIT_BOOL_TYPE));
      final NodeVariable varBVNORR_ODD_BITS =
          new NodeVariable(builder.addVariable("varBVNORR_ODD_BITS", BIT_BOOL_TYPE));

      final NodeVariable varBVXORR_NO_BITS =
          new NodeVariable(builder.addVariable("varBVXORR_NO_BITS", BIT_BOOL_TYPE));
      final NodeVariable varBVXORR_ALL_BITS =
          new NodeVariable(builder.addVariable("varBVXORR_ALL_BITS", BIT_BOOL_TYPE));
      final NodeVariable varBVXORR_EVEN_BITS =
          new NodeVariable(builder.addVariable("varBVXORR_EVEN_BITS", BIT_BOOL_TYPE));
      final NodeVariable varBVXORR_ODD_BITS =
          new NodeVariable(builder.addVariable("varBVXORR_ODD_BITS", BIT_BOOL_TYPE));

      final NodeVariable varBVXNORR_NO_BITS =
          new NodeVariable(builder.addVariable("varBVXNORR_NO_BITS", BIT_BOOL_TYPE));
      final NodeVariable varBVXNORR_ALL_BITS =
          new NodeVariable(builder.addVariable("varBVXNORR_ALL_BITS", BIT_BOOL_TYPE));
      final NodeVariable varBVXNORR_EVEN_BITS =
          new NodeVariable(builder.addVariable("varBVXNORR_EVEN_BITS", BIT_BOOL_TYPE));
      final NodeVariable varBVXNORR_ODD_BITS =
          new NodeVariable(builder.addVariable("varBVXNORR_ODD_BITS", BIT_BOOL_TYPE));

      final Formulas formulas = new Formulas();
      builder.setInnerRep(formulas);

      // BVANDR Asserts
      formulas.add(Nodes.eq(varBVANDR_NO_BITS,   Nodes.bvandr(NO_BITS)));
      formulas.add(Nodes.eq(varBVANDR_ALL_BITS,  Nodes.bvandr(ALL_BITS)));
      formulas.add(Nodes.eq(varBVANDR_EVEN_BITS, Nodes.bvandr(EVEN_BITS)));
      formulas.add(Nodes.eq(varBVANDR_ODD_BITS,  Nodes.bvandr(ODD_BITS)));

      // BVNANDR Asserts
      formulas.add(Nodes.eq(varBVNANDR_NO_BITS,   Nodes.bvnandr(NO_BITS)));
      formulas.add(Nodes.eq(varBVNANDR_ALL_BITS,  Nodes.bvnandr(ALL_BITS)));
      formulas.add(Nodes.eq(varBVNANDR_EVEN_BITS, Nodes.bvnandr(EVEN_BITS)));
      formulas.add(Nodes.eq(varBVNANDR_ODD_BITS,  Nodes.bvnandr(ODD_BITS)));

      // BVORR Asserts
      formulas.add(Nodes.eq(varBVORR_NO_BITS,   Nodes.bvorr(NO_BITS)));
      formulas.add(Nodes.eq(varBVORR_ALL_BITS,  Nodes.bvorr(ALL_BITS)));
      formulas.add(Nodes.eq(varBVORR_EVEN_BITS, Nodes.bvorr(EVEN_BITS)));
      formulas.add(Nodes.eq(varBVORR_ODD_BITS,  Nodes.bvorr(ODD_BITS)));

      // BVNORR Asserts
      formulas.add(Nodes.eq(varBVNORR_NO_BITS,   Nodes.BVNORR(NO_BITS)));
      formulas.add(Nodes.eq(varBVNORR_ALL_BITS,  Nodes.BVNORR(ALL_BITS)));
      formulas.add(Nodes.eq(varBVNORR_EVEN_BITS, Nodes.BVNORR(EVEN_BITS)));
      formulas.add(Nodes.eq(varBVNORR_ODD_BITS,  Nodes.BVNORR(ODD_BITS)));

      // BVXORR Asserts
      formulas.add(Nodes.eq(varBVXORR_NO_BITS,   Nodes.BVXORR(NO_BITS)));
      formulas.add(Nodes.eq(varBVXORR_ALL_BITS,  Nodes.BVXORR(ALL_BITS)));
      formulas.add(Nodes.eq(varBVXORR_EVEN_BITS, Nodes.BVXORR(EVEN_BITS)));
      formulas.add(Nodes.eq(varBVXORR_ODD_BITS,  Nodes.BVXORR(ODD_BITS)));

      // BVXNORR Asserts

      formulas.add(Nodes.eq(varBVXNORR_NO_BITS,   Nodes.BVXNORR(NO_BITS)));
      formulas.add(Nodes.eq(varBVXNORR_ALL_BITS,  Nodes.BVXNORR(ALL_BITS)));
      formulas.add(Nodes.eq(varBVXNORR_EVEN_BITS, Nodes.BVXNORR(EVEN_BITS)));
      formulas.add(Nodes.eq(varBVXNORR_ODD_BITS,  Nodes.BVXNORR(ODD_BITS)));

      return builder.build();
    }

    @Override
    public Iterable<Variable> getExpectedVariables() {
      return Arrays.asList(new Variable("varBVANDR_NO_BITS", BIT_FALSE), new Variable(
          "varBVANDR_ALL_BITS", BIT_TRUE), new Variable("varBVANDR_EVEN_BITS", BIT_FALSE),
          new Variable("varBVANDR_ODD_BITS", BIT_FALSE),

          new Variable("varBVNANDR_NO_BITS", BIT_TRUE), new Variable("varBVNANDR_ALL_BITS",
              BIT_FALSE), new Variable("varBVNANDR_EVEN_BITS", BIT_TRUE), new Variable(
              "varBVNANDR_ODD_BITS", BIT_TRUE),

          new Variable("varBVORR_NO_BITS", BIT_FALSE), new Variable("varBVORR_ALL_BITS", BIT_TRUE),
          new Variable("varBVORR_EVEN_BITS", BIT_TRUE),
          new Variable("varBVORR_ODD_BITS", BIT_TRUE),

          new Variable("varBVNORR_NO_BITS", BIT_TRUE),
          new Variable("varBVNORR_ALL_BITS", BIT_FALSE), new Variable("varBVNORR_EVEN_BITS",
              BIT_FALSE), new Variable("varBVNORR_ODD_BITS", BIT_FALSE),

          new Variable("varBVXORR_NO_BITS", BIT_FALSE), new Variable("varBVXORR_ALL_BITS",
              BIT_FALSE), new Variable("varBVXORR_EVEN_BITS", BIT_FALSE), new Variable(
              "varBVXORR_ODD_BITS", BIT_TRUE),

          new Variable("varBVXNORR_NO_BITS", BIT_TRUE), new Variable("varBVXNORR_ALL_BITS",
              BIT_TRUE), new Variable("varBVXNORR_EVEN_BITS", BIT_TRUE), new Variable(
              "varBVXNORR_ODD_BITS", BIT_FALSE));
    }
  }
}
