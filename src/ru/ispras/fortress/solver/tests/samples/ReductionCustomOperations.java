package ru.ispras.fortress.solver.tests.samples;

import java.util.Arrays;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeExpr;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.solver.Solver;
import ru.ispras.fortress.solver.SolverId;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintBuilder;
import ru.ispras.fortress.solver.constraint.ConstraintKind;
import ru.ispras.fortress.solver.constraint.Formulas;
import ru.ispras.fortress.solver.function.FunctionFactory;
import ru.ispras.fortress.solver.function.FunctionOperation;

public class ReductionCustomOperations implements ISampleConstraint
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
        registerOperations();

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

        /*
        // TODO: BVXORR IS NOT IMPLEMENTED
        final NodeVariable varBVXORR_NO_BITS   = new NodeVariable(builder.addVariable("varBVXORR_NO_BITS",   BIT_BOOL_TYPE));
        final NodeVariable varBVXORR_ALL_BITS  = new NodeVariable(builder.addVariable("varBVXORR_ALL_BITS",  BIT_BOOL_TYPE));
        final NodeVariable varBVXORR_EVEN_BITS = new NodeVariable(builder.addVariable("varBVXORR_EVEN_BITS", BIT_BOOL_TYPE));
        final NodeVariable varBVXORR_ODD_BITS  = new NodeVariable(builder.addVariable("varBVXORR_ODD_BITS",  BIT_BOOL_TYPE));
        
        // TODO: BVXNORR IS NOT IMPLEMENTED
        final NodeVariable varBVXNORR_NO_BITS   = new NodeVariable(builder.addVariable("varBVXNORR_NO_BITS",   BIT_BOOL_TYPE));
        final NodeVariable varBVXNORR_ALL_BITS  = new NodeVariable(builder.addVariable("varBVXNORR_ALL_BITS",  BIT_BOOL_TYPE));
        final NodeVariable varBVXNORR_EVEN_BITS = new NodeVariable(builder.addVariable("varBVXNORR_EVEN_BITS", BIT_BOOL_TYPE));
        final NodeVariable varBVXNORR_ODD_BITS  = new NodeVariable(builder.addVariable("varBVXNORR_ODD_BITS",  BIT_BOOL_TYPE));
        */

        final Formulas formulas = new Formulas();
        builder.setInnerRep(formulas);

        // BVANDR Asserts

        formulas.add(new NodeExpr(
            StandardOperation.EQ, varBVANDR_NO_BITS, new NodeExpr(FunctionOperation.BVANDR, NO_BITS)));

        formulas.add(new NodeExpr(
            StandardOperation.EQ, varBVANDR_ALL_BITS, new NodeExpr(FunctionOperation.BVANDR, ALL_BITS)));

        formulas.add(new NodeExpr(
            StandardOperation.EQ, varBVANDR_EVEN_BITS, new NodeExpr(FunctionOperation.BVANDR, EVEN_BITS)));

        formulas.add(new NodeExpr(
            StandardOperation.EQ, varBVANDR_ODD_BITS, new NodeExpr(FunctionOperation.BVANDR, ODD_BITS)));

        // BVNANDR Asserts

        formulas.add(new NodeExpr(
            StandardOperation.EQ, varBVNANDR_NO_BITS, new NodeExpr(FunctionOperation.BVNANDR, NO_BITS)));

        formulas.add(new NodeExpr(
            StandardOperation.EQ, varBVNANDR_ALL_BITS, new NodeExpr(FunctionOperation.BVNANDR, ALL_BITS)));

        formulas.add(new NodeExpr(
            StandardOperation.EQ, varBVNANDR_EVEN_BITS, new NodeExpr(FunctionOperation.BVNANDR, EVEN_BITS)));

        formulas.add(new NodeExpr(
            StandardOperation.EQ, varBVNANDR_ODD_BITS, new NodeExpr(FunctionOperation.BVNANDR, ODD_BITS)));

        // BVORR Asserts

        formulas.add(new NodeExpr(
            StandardOperation.EQ, varBVORR_NO_BITS, new NodeExpr(FunctionOperation.BVORR, NO_BITS)));

        formulas.add(new NodeExpr(
            StandardOperation.EQ, varBVORR_ALL_BITS, new NodeExpr(FunctionOperation.BVORR, ALL_BITS)));

        formulas.add(new NodeExpr(
            StandardOperation.EQ, varBVORR_EVEN_BITS, new NodeExpr(FunctionOperation.BVORR, EVEN_BITS)));

        formulas.add(new NodeExpr(
            StandardOperation.EQ, varBVORR_ODD_BITS, new NodeExpr(FunctionOperation.BVORR, ODD_BITS)));

        // BVNORR Asserts

        formulas.add(new NodeExpr(
            StandardOperation.EQ, varBVNORR_NO_BITS, new NodeExpr(FunctionOperation.BVNORR, NO_BITS)));

        formulas.add(new NodeExpr(
            StandardOperation.EQ, varBVNORR_ALL_BITS, new NodeExpr(FunctionOperation.BVNORR, ALL_BITS)));

        formulas.add(new NodeExpr(
            StandardOperation.EQ, varBVNORR_EVEN_BITS, new NodeExpr(FunctionOperation.BVNORR, EVEN_BITS)));

        formulas.add(new NodeExpr(
            StandardOperation.EQ, varBVNORR_ODD_BITS, new NodeExpr(FunctionOperation.BVNORR, ODD_BITS)));
        
        /*
        // BVXORR Asserts

        formulas.add(new NodeExpr(
            StandardOperation.EQ, varBVXORR_NO_BITS, new NodeExpr(FunctionOperation.BVXORR, NO_BITS)));

        formulas.add(new NodeExpr(
            StandardOperation.EQ, varBVXORR_ALL_BITS, new NodeExpr(FunctionOperation.BVXORR, ALL_BITS)));

        formulas.add(new NodeExpr(
            StandardOperation.EQ, varBVXORR_EVEN_BITS, new NodeExpr(FunctionOperation.BVXORR, EVEN_BITS)));

        formulas.add(new NodeExpr(
            StandardOperation.EQ, varBVXORR_ODD_BITS, new NodeExpr(FunctionOperation.BVXORR, ODD_BITS)));

        // BVXNORR Asserts

        formulas.add(new NodeExpr(
            StandardOperation.EQ, varBVXNORR_NO_BITS, new NodeExpr(FunctionOperation.BVXNORR, NO_BITS)));

        formulas.add(new NodeExpr(
            StandardOperation.EQ, varBVXNORR_ALL_BITS, new NodeExpr(FunctionOperation.BVXNORR, ALL_BITS)));

        formulas.add(new NodeExpr(
            StandardOperation.EQ, varBVXNORR_EVEN_BITS, new NodeExpr(FunctionOperation.BVXNORR, EVEN_BITS)));

        formulas.add(new NodeExpr(
            StandardOperation.EQ, varBVXNORR_ODD_BITS, new NodeExpr(FunctionOperation.BVXNORR, ODD_BITS)));
        */

        return builder.build();
    }

    private void registerOperations()
    {
        final Solver solver = SolverId.Z3_TEXT.getSolver();
        assert solver != null;

        solver.addCustomOperation(
            FunctionOperation.BVANDR,
            FunctionFactory.makeBVANDR(new Variable("x", BIT_VECTOR_TYPE))
        );

        solver.addCustomOperation(
            FunctionOperation.BVNANDR,
            FunctionFactory.makeBVNANDR(new Variable("x", BIT_VECTOR_TYPE))
        );

        solver.addCustomOperation(
            FunctionOperation.BVORR,
            FunctionFactory.makeBVORR(new Variable("x", BIT_VECTOR_TYPE))
        );

        solver.addCustomOperation(
            FunctionOperation.BVNORR,
            FunctionFactory.makeBVNORR(new Variable("x", BIT_VECTOR_TYPE))
        );

        /*
        // TODO: BVXORR IS NOT IMPLEMENTED
        solver.addCustomOperation(
            FunctionOperation.BVXORR,
            FunctionFactory.makeBVXORR(new Variable("x", BIT_VECTOR_TYPE))
        );

        // TODO: BVXNORR IS NOT IMPLEMENTED
        solver.addCustomOperation(
            FunctionOperation.BVXNORR,
            FunctionFactory.makeBVXNORR(new Variable("x", BIT_VECTOR_TYPE))
        );
        */
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
            new Variable("varBVNORR_ODD_BITS",  BIT_FALSE)

            /*
            // TODO: BVXORR IS NOT IMPLEMENTED
            new Variable("varBVXORR_NO_BITS",    BIT_FALSE),
            new Variable("varBVXORR_ALL_BITS",   BIT_FALSE),
            new Variable("varBVXORR_EVEN_BITS",  BIT_FALSE),
            new Variable("varBVXORR_ODD_BITS",   BIT_TRUE),
            
            // TODO: BVXNORR IS NOT IMPLEMENTED
            new Variable("varBVXNORR_NO_BITS",   BIT_TRUE),
            new Variable("varBVXNORR_ALL_BITS",  BIT_TRUE),
            new Variable("varBVXNORR_EVEN_BITS", BIT_TRUE),
            new Variable("varBVXNORR_ODD_BITS",  BIT_FALSE)
            */
            );
    }
}
