package ru.ispras.fortress.solver;

import java.util.ArrayList;
import java.util.List;

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

public class UnaryOperationsTestCase extends GenericSolverSampleTestBase
{
    @Override
    public ISampleConstraint createSample()
    {
        return new UnaryOperations();
    }

    /** 
    The constraint as described in the SMT-LIB language:

    <pre>
    (declare-const a Int)
    (declare-const b Int)
    (assert (= (~ a) 5))
    (assert (= (+ b) 1))
    (check-sat)
    (get-value (a b))
    (exit)</pre>

    Expected output: sat ((x (- 5)) (y 1))
    */

    public static class UnaryOperations implements ISampleConstraint
    {
        private static final DataType intType = DataType.INTEGER;

        @Override
        public Constraint getConstraint()
        {
            final ConstraintBuilder builder = new ConstraintBuilder();

            builder.setName("UnaryOperations");
            builder.setKind(ConstraintKind.FORMULA_BASED);
            builder.setDescription("Unary Operations constraint");

            final NodeVariable a = new NodeVariable(builder.addVariable("a", intType));
            final NodeVariable b = new NodeVariable(builder.addVariable("b", intType));

            final Formulas formulas = new Formulas();
            builder.setInnerRep(formulas);

            formulas.add(
                new NodeOperation(
                    StandardOperation.EQ,
                    new NodeOperation(StandardOperation.MINUS, a),
                    new NodeValue(intType.valueOf("5", 10))
                )
            );

            formulas.add(
                new NodeOperation(
                    StandardOperation.EQ,
                    new NodeOperation(StandardOperation.PLUS, b),
                    new NodeValue(intType.valueOf("1", 10))
                )
            );

            return builder.build();
        }

        @Override
        public Iterable<Variable> getExpectedVariables()
        {
            final List<Variable> result = new ArrayList<Variable>();

            result.add(new Variable("a", intType.valueOf("-5", 10)));
            result.add(new Variable("b", intType.valueOf("1", 10)));

            return result;
        }
    }
}
