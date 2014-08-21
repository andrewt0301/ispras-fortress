package ru.ispras.fortress.solver;

import java.util.ArrayList;
import java.util.List;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintBuilder;
import ru.ispras.fortress.solver.constraint.ConstraintKind;
import ru.ispras.fortress.solver.constraint.Formulas;

public class AbsCustomOperationTestCase extends GenericSolverSampleTestBase
{
    @Override
    public ISampleConstraint createSample()
    {
        return new AbsCustomOperation();
    }

    /** The constraint as described in the SMT language:
	<pre>
    (declare-const a Real)
    (declare-const b Real)
    (declare-const c Int)
    (declare-const d Int)
    (define-fun StandardOperation_ABS_RET_LOGIC_REAL_PARAMS_LOGIC_REAL ((x Real)) Real (ite (>= x 0.0) x (- x)))
    (define-fun StandardOperation_ABS_RET_LOGIC_INTEGER_PARAMS_LOGIC_INTEGER ((x Int)) Int (ite (>= x 0) x (- x)))
    (assert  (< a 0.0))
    (assert  (> b 0.0))
    (assert  (< c 0))
    (assert  (> d 0))
    (assert  (= (StandardOperation_ABS_RET_LOGIC_REAL_PARAMS_LOGIC_REAL (- 5.0)) 5.0))
    (assert  (= (StandardOperation_ABS_RET_LOGIC_REAL_PARAMS_LOGIC_REAL 5.0) 5.0))
    (assert  (= (StandardOperation_ABS_RET_LOGIC_REAL_PARAMS_LOGIC_REAL (- a)) 5.0))
    (assert  (= (StandardOperation_ABS_RET_LOGIC_REAL_PARAMS_LOGIC_REAL b) 5.0))
    (assert  (= (StandardOperation_ABS_RET_LOGIC_INTEGER_PARAMS_LOGIC_INTEGER (- c)) 5))
    (assert  (= (StandardOperation_ABS_RET_LOGIC_INTEGER_PARAMS_LOGIC_INTEGER d) 5))
    (check-sat)
    (get-value ( a b c d))
    (get-model)
    (exit)
    </pre>

    Expected output: sat ((a (- 5.0)) (b 5.0) (c (- 5)) (d 5))
    */

    public static class AbsCustomOperation implements ISampleConstraint
    {
        @Override
        public Constraint getConstraint()
        {
            final ConstraintBuilder builder = new ConstraintBuilder();

            builder.setName("AbsCustomOperation");
            builder.setKind(ConstraintKind.FORMULA_BASED);
            builder.setDescription("AbsCustomOperation constraint");

            final NodeVariable a = new NodeVariable(builder.addVariable("a", DataType.REAL));
            final NodeVariable b = new NodeVariable(builder.addVariable("b", DataType.REAL));
            final NodeVariable c = new NodeVariable(builder.addVariable("c", DataType.INTEGER));
            final NodeVariable d = new NodeVariable(builder.addVariable("d", DataType.INTEGER));

            final Formulas formulas = new Formulas();
            builder.setInnerRep(formulas);
            
            formulas.add(new NodeOperation(
                StandardOperation.LESS, a, NodeValue.newReal(0)));
            
            formulas.add(new NodeOperation(
                StandardOperation.GREATER, b, NodeValue.newReal(0)));

            formulas.add(new NodeOperation(
                StandardOperation.LESS, c, NodeValue.newInteger(0)));
            
            formulas.add(new NodeOperation(
                StandardOperation.GREATER, d, NodeValue.newInteger(0)));

            formulas.add(
                new NodeOperation(
                    StandardOperation.EQ,
                    new NodeOperation(
                        StandardOperation.ABS,
                        new NodeOperation(StandardOperation.MINUS, NodeValue.newReal(5.0))
                    ),
                    NodeValue.newReal(5.0)
                )
            );

            formulas.add(
                new NodeOperation(
                    StandardOperation.EQ,
                    new NodeOperation(
                        StandardOperation.ABS,
                        NodeValue.newReal(5.0)
                    ),
                    NodeValue.newReal(5.0)
                )
            );

            formulas.add(
                new NodeOperation(
                    StandardOperation.EQ,
                    new NodeOperation(
                        StandardOperation.ABS,
                        new NodeOperation(StandardOperation.MINUS, a)
                    ),
                    NodeValue.newReal(5.0)
                )
            );

            formulas.add(
                new NodeOperation(
                    StandardOperation.EQ,
                    new NodeOperation(StandardOperation.ABS, b),
                    NodeValue.newReal(5.0)
                )
            );
            
            formulas.add(
                new NodeOperation(
                    StandardOperation.EQ,
                    new NodeOperation(
                        StandardOperation.ABS,
                        new NodeOperation(StandardOperation.MINUS, c)
                    ),
                    NodeValue.newInteger(5)
                )
            );

            formulas.add(
                new NodeOperation(
                    StandardOperation.EQ,
                    new NodeOperation(StandardOperation.ABS, d),
                    NodeValue.newInteger(5)
                )
            );

            return builder.build();
        }

        @Override
        public Iterable<Variable> getExpectedVariables()
        {
            final List<Variable> result = new ArrayList<Variable>();

            result.add(new Variable("a", Data.newReal(-5.0)));
            result.add(new Variable("b", Data.newReal(5.0)));
            result.add(new Variable("c", Data.newInteger(-5)));
            result.add(new Variable("d", Data.newInteger(5)));

            return result;
        }
    }
}
