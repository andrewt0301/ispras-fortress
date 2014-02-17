package ru.ispras.fortress.solver;

import java.util.ArrayList;
import java.util.List;

import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.NodeExpr;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.solver.common.GenericSolverSampleTestBase;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintBuilder;
import ru.ispras.fortress.solver.constraint.ConstraintCombiner;
import ru.ispras.fortress.solver.constraint.Formulas;
import ru.ispras.fortress.solver.samples.BVUGTOperation;
import ru.ispras.fortress.solver.samples.ISampleConstraint;

public class ConstraintConjunctionTestCase extends GenericSolverSampleTestBase
{
    @Override
    public ISampleConstraint createSample()
    {
        return new ConstraintConjunction();
    }
    
    public static class ConstraintConjunction extends BVUGTOperation
    {
        @Override
        public Constraint getConstraint()
        {
            final Constraint  constraint = super.getConstraint();
            final Constraint         neg = ConstraintCombiner.makeNegation(constraint);
            final Constraint conjunction = ConstraintCombiner.makeConjunction(constraint, neg);

            final ConstraintBuilder builder = new ConstraintBuilder();

            builder.setKind(constraint.getKind());
            builder.setName(conjunction.getName());

            for (Variable var : conjunction.getVariables())
                builder.addVariable(var.getName(), var.getData());

            final Formulas formulas = new Formulas();
            builder.setInnerRep(formulas);

            formulas.add(
                new NodeExpr(
                    StandardOperation.NOT,
                    new NodeExpr(
                        StandardOperation.AND, 
                        ((Formulas)conjunction.getInnerRep()).exprs().iterator().next(), 
                        ((Formulas)conjunction.getInnerRep()).exprs().iterator().next()
                    )
                )
            );

            return builder.build();
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
