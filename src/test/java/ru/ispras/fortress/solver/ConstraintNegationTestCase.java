package ru.ispras.fortress.solver;

import java.util.ArrayList;
import java.util.List;

import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintBuilder;
import ru.ispras.fortress.solver.constraint.ConstraintCombiner;
import ru.ispras.fortress.solver.constraint.Formulas;

public class ConstraintNegationTestCase extends GenericSolverSampleTestBase
{
    @Override
    public ISampleConstraint createSample()
    {
        return new ConstraintNegation();
    }

    public static class ConstraintNegation extends BVUGTOperation
    {
        public Constraint getConstraint()
        {
            final Constraint constraint = super.getConstraint();
            final Node formula = ((Formulas)constraint.getInnerRep()).exprs().iterator().next();

            final Constraint neg = ConstraintCombiner.makeNegation(constraint);
            final Node negFormula = ((Formulas)neg.getInnerRep()).exprs().iterator().next();

            final ConstraintBuilder builder = new ConstraintBuilder();

            builder.setName("Negation constraint.");
            builder.setKind(constraint.getKind());

            for (Variable var : constraint.getVariables())
                builder.addVariable(var.getName(), var.getData());

            final Formulas formulas = new Formulas();
            builder.setInnerRep(formulas);

            // not(= (a not(not(a))))
            formulas.add(
                new NodeOperation(
                    StandardOperation.NOT,
                    new NodeOperation(
                        StandardOperation.EQ,
                        formula,
                        new NodeOperation(
                            StandardOperation.NOT,
                            negFormula
                        )
                    )
                )
            );

            // (not(a) and a)
            formulas.add(
                new NodeOperation(
                    StandardOperation.AND,
                    negFormula,
                    formula
                )
            );

            // not((not(a)) or a)
            formulas.add(
                new NodeOperation(
                    StandardOperation.NOT,
                    new NodeOperation(
                        StandardOperation.OR,
                        negFormula,
                        formula
                    )
                )
            );

            return ConstraintCombiner.makeNegation(builder.build());
        }

        @Override
        public Iterable<Variable> getExpectedVariables()
        {
            final List<Variable> result = new ArrayList<Variable>();
            
            result.add(new Variable("x", BIT_VECTOR_TYPE.valueOf("0", 10)));

            return result;
        }
    }
}
