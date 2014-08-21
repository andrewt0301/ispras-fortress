package ru.ispras.fortress.solver;

import java.util.Arrays;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintBuilder;
import ru.ispras.fortress.solver.constraint.ConstraintKind;
import ru.ispras.fortress.solver.constraint.Formulas;

public class ReductionCustomOperationsTestCase extends GenericSolverSampleTestBase
{
    @Override
    public ISampleConstraint createSample()
    {
        return new ReductionCustomOperations();
    }

    public static class ReductionCustomOperations implements ISampleConstraint
    {
        // Data Types and Constants
        private static final int      BIT_VECTOR_SIZE = 8;
        private static final DataType BIT_VECTOR_TYPE = DataType.BIT_VECTOR(BIT_VECTOR_SIZE);

        private static final int        BIT_BOOL_SIZE = 1;
        private static final DataType   BIT_BOOL_TYPE = DataType.BIT_VECTOR(BIT_BOOL_SIZE);

        private static final Data  BIT_TRUE = Data.newBitVector(1, BIT_BOOL_SIZE);
        private static final Data BIT_FALSE = Data.newBitVector(0, BIT_BOOL_SIZE);

        // Test Data Constants
        private static final Node   NO_BITS = new NodeValue(BIT_VECTOR_TYPE.valueOf("00000000", 2));
        private static final Node  ALL_BITS = new NodeValue(BIT_VECTOR_TYPE.valueOf("11111111", 2));
        private static final Node EVEN_BITS = new NodeValue(BIT_VECTOR_TYPE.valueOf("00111100", 2));
        private static final Node  ODD_BITS = new NodeValue(BIT_VECTOR_TYPE.valueOf("10000000", 2));

        @Override
        public Constraint getConstraint()
        {
            final ConstraintBuilder builder = new ConstraintBuilder();

            builder.setName("ReductionCustomOperations");
            builder.setKind(ConstraintKind.FORMULA_BASED);
            builder.setDescription("Constraint to test reduction operations (Verilog-like).");

            final NodeVariable varBVANDR_NO_BITS   = new NodeVariable(builder.addVariable("varBVANDR_NO_BITS",   BIT_BOOL_TYPE));
            final NodeVariable varBVANDR_ALL_BITS  = new NodeVariable(builder.addVariable("varBVANDR_ALL_BITS",  BIT_BOOL_TYPE));
            final NodeVariable varBVANDR_EVEN_BITS = new NodeVariable(builder.addVariable("varBVANDR_EVEN_BITS", BIT_BOOL_TYPE));
            final NodeVariable varBVANDR_ODD_BITS  = new NodeVariable(builder.addVariable("varBVANDR_ODD_BITS",  BIT_BOOL_TYPE));
            
            final NodeVariable varBVNANDR_NO_BITS   = new NodeVariable(builder.addVariable("varBVNANDR_NO_BITS",   BIT_BOOL_TYPE));
            final NodeVariable varBVNANDR_ALL_BITS  = new NodeVariable(builder.addVariable("varBVNANDR_ALL_BITS",  BIT_BOOL_TYPE));
            final NodeVariable varBVNANDR_EVEN_BITS = new NodeVariable(builder.addVariable("varBVNANDR_EVEN_BITS", BIT_BOOL_TYPE));
            final NodeVariable varBVNANDR_ODD_BITS  = new NodeVariable(builder.addVariable("varBVNANDR_ODD_BITS",  BIT_BOOL_TYPE));
            
            final NodeVariable varBVORR_NO_BITS   = new NodeVariable(builder.addVariable("varBVORR_NO_BITS",   BIT_BOOL_TYPE));
            final NodeVariable varBVORR_ALL_BITS  = new NodeVariable(builder.addVariable("varBVORR_ALL_BITS",  BIT_BOOL_TYPE));
            final NodeVariable varBVORR_EVEN_BITS = new NodeVariable(builder.addVariable("varBVORR_EVEN_BITS", BIT_BOOL_TYPE));
            final NodeVariable varBVORR_ODD_BITS  = new NodeVariable(builder.addVariable("varBVORR_ODD_BITS",  BIT_BOOL_TYPE));

            final NodeVariable varBVNORR_NO_BITS   = new NodeVariable(builder.addVariable("varBVNORR_NO_BITS",   BIT_BOOL_TYPE));
            final NodeVariable varBVNORR_ALL_BITS  = new NodeVariable(builder.addVariable("varBVNORR_ALL_BITS",  BIT_BOOL_TYPE));
            final NodeVariable varBVNORR_EVEN_BITS = new NodeVariable(builder.addVariable("varBVNORR_EVEN_BITS", BIT_BOOL_TYPE));
            final NodeVariable varBVNORR_ODD_BITS  = new NodeVariable(builder.addVariable("varBVNORR_ODD_BITS",  BIT_BOOL_TYPE));

            final NodeVariable varBVXORR_NO_BITS   = new NodeVariable(builder.addVariable("varBVXORR_NO_BITS",   BIT_BOOL_TYPE));
            final NodeVariable varBVXORR_ALL_BITS  = new NodeVariable(builder.addVariable("varBVXORR_ALL_BITS",  BIT_BOOL_TYPE));
            final NodeVariable varBVXORR_EVEN_BITS = new NodeVariable(builder.addVariable("varBVXORR_EVEN_BITS", BIT_BOOL_TYPE));
            final NodeVariable varBVXORR_ODD_BITS  = new NodeVariable(builder.addVariable("varBVXORR_ODD_BITS",  BIT_BOOL_TYPE));
            
            final NodeVariable varBVXNORR_NO_BITS   = new NodeVariable(builder.addVariable("varBVXNORR_NO_BITS",   BIT_BOOL_TYPE));
            final NodeVariable varBVXNORR_ALL_BITS  = new NodeVariable(builder.addVariable("varBVXNORR_ALL_BITS",  BIT_BOOL_TYPE));
            final NodeVariable varBVXNORR_EVEN_BITS = new NodeVariable(builder.addVariable("varBVXNORR_EVEN_BITS", BIT_BOOL_TYPE));
            final NodeVariable varBVXNORR_ODD_BITS  = new NodeVariable(builder.addVariable("varBVXNORR_ODD_BITS",  BIT_BOOL_TYPE));

            final Formulas formulas = new Formulas();
            builder.setInnerRep(formulas);

            // BVANDR Asserts

            formulas.add(new NodeOperation(
                StandardOperation.EQ, varBVANDR_NO_BITS, new NodeOperation(StandardOperation.BVANDR, NO_BITS)));

            formulas.add(new NodeOperation(
                StandardOperation.EQ, varBVANDR_ALL_BITS, new NodeOperation(StandardOperation.BVANDR, ALL_BITS)));

            formulas.add(new NodeOperation(
                StandardOperation.EQ, varBVANDR_EVEN_BITS, new NodeOperation(StandardOperation.BVANDR, EVEN_BITS)));

            formulas.add(new NodeOperation(
                StandardOperation.EQ, varBVANDR_ODD_BITS, new NodeOperation(StandardOperation.BVANDR, ODD_BITS)));

            // BVNANDR Asserts

            formulas.add(new NodeOperation(
                StandardOperation.EQ, varBVNANDR_NO_BITS, new NodeOperation(StandardOperation.BVNANDR, NO_BITS)));

            formulas.add(new NodeOperation(
                StandardOperation.EQ, varBVNANDR_ALL_BITS, new NodeOperation(StandardOperation.BVNANDR, ALL_BITS)));

            formulas.add(new NodeOperation(
                StandardOperation.EQ, varBVNANDR_EVEN_BITS, new NodeOperation(StandardOperation.BVNANDR, EVEN_BITS)));

            formulas.add(new NodeOperation(
                StandardOperation.EQ, varBVNANDR_ODD_BITS, new NodeOperation(StandardOperation.BVNANDR, ODD_BITS)));

            // BVORR Asserts

            formulas.add(new NodeOperation(
                StandardOperation.EQ, varBVORR_NO_BITS, new NodeOperation(StandardOperation.BVORR, NO_BITS)));

            formulas.add(new NodeOperation(
                StandardOperation.EQ, varBVORR_ALL_BITS, new NodeOperation(StandardOperation.BVORR, ALL_BITS)));

            formulas.add(new NodeOperation(
                StandardOperation.EQ, varBVORR_EVEN_BITS, new NodeOperation(StandardOperation.BVORR, EVEN_BITS)));

            formulas.add(new NodeOperation(
                StandardOperation.EQ, varBVORR_ODD_BITS, new NodeOperation(StandardOperation.BVORR, ODD_BITS)));

            // BVNORR Asserts

            formulas.add(new NodeOperation(
                StandardOperation.EQ, varBVNORR_NO_BITS, new NodeOperation(StandardOperation.BVNORR, NO_BITS)));

            formulas.add(new NodeOperation(
                StandardOperation.EQ, varBVNORR_ALL_BITS, new NodeOperation(StandardOperation.BVNORR, ALL_BITS)));

            formulas.add(new NodeOperation(
                StandardOperation.EQ, varBVNORR_EVEN_BITS, new NodeOperation(StandardOperation.BVNORR, EVEN_BITS)));

            formulas.add(new NodeOperation(
                StandardOperation.EQ, varBVNORR_ODD_BITS, new NodeOperation(StandardOperation.BVNORR, ODD_BITS)));
            
            // BVXORR Asserts

            formulas.add(new NodeOperation(
                StandardOperation.EQ, varBVXORR_NO_BITS, new NodeOperation(StandardOperation.BVXORR, NO_BITS)));

            formulas.add(new NodeOperation(
                StandardOperation.EQ, varBVXORR_ALL_BITS, new NodeOperation(StandardOperation.BVXORR, ALL_BITS)));

            formulas.add(new NodeOperation(
                StandardOperation.EQ, varBVXORR_EVEN_BITS, new NodeOperation(StandardOperation.BVXORR, EVEN_BITS)));

            formulas.add(new NodeOperation(
                StandardOperation.EQ, varBVXORR_ODD_BITS, new NodeOperation(StandardOperation.BVXORR, ODD_BITS)));

            // BVXNORR Asserts

            formulas.add(new NodeOperation(
                StandardOperation.EQ, varBVXNORR_NO_BITS, new NodeOperation(StandardOperation.BVXNORR, NO_BITS)));

            formulas.add(new NodeOperation(
                StandardOperation.EQ, varBVXNORR_ALL_BITS, new NodeOperation(StandardOperation.BVXNORR, ALL_BITS)));

            formulas.add(new NodeOperation(
                StandardOperation.EQ, varBVXNORR_EVEN_BITS, new NodeOperation(StandardOperation.BVXNORR, EVEN_BITS)));

            formulas.add(new NodeOperation(
                StandardOperation.EQ, varBVXNORR_ODD_BITS, new NodeOperation(StandardOperation.BVXNORR, ODD_BITS)));

            return builder.build();
        }

        @Override
        public Iterable<Variable> getExpectedVariables()
        {
            return Arrays.asList(
                new Variable("varBVANDR_NO_BITS",    BIT_FALSE),
                new Variable("varBVANDR_ALL_BITS",   BIT_TRUE),
                new Variable("varBVANDR_EVEN_BITS",  BIT_FALSE),
                new Variable("varBVANDR_ODD_BITS",   BIT_FALSE),

                new Variable("varBVNANDR_NO_BITS",   BIT_TRUE),
                new Variable("varBVNANDR_ALL_BITS",  BIT_FALSE),
                new Variable("varBVNANDR_EVEN_BITS", BIT_TRUE),
                new Variable("varBVNANDR_ODD_BITS",  BIT_TRUE),

                new Variable("varBVORR_NO_BITS",    BIT_FALSE),
                new Variable("varBVORR_ALL_BITS",   BIT_TRUE),
                new Variable("varBVORR_EVEN_BITS",  BIT_TRUE),
                new Variable("varBVORR_ODD_BITS",   BIT_TRUE),

                new Variable("varBVNORR_NO_BITS",   BIT_TRUE),
                new Variable("varBVNORR_ALL_BITS",  BIT_FALSE),
                new Variable("varBVNORR_EVEN_BITS", BIT_FALSE),
                new Variable("varBVNORR_ODD_BITS",  BIT_FALSE),

                new Variable("varBVXORR_NO_BITS",    BIT_FALSE),
                new Variable("varBVXORR_ALL_BITS",   BIT_FALSE),
                new Variable("varBVXORR_EVEN_BITS",  BIT_FALSE),
                new Variable("varBVXORR_ODD_BITS",   BIT_TRUE),
                
                new Variable("varBVXNORR_NO_BITS",   BIT_TRUE),
                new Variable("varBVXNORR_ALL_BITS",  BIT_TRUE),
                new Variable("varBVXNORR_EVEN_BITS", BIT_TRUE),
                new Variable("varBVXNORR_ODD_BITS",  BIT_FALSE)
            );
        }
    }
}
