package ru.ispras.fortress.solver.samples;

import java.util.ArrayList;
import java.util.List;

import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintCombiner;

public class ConstraintDisjunction extends BVUGTOperation
{
    public Constraint getConstraint()
    {
        final Constraint constraint = super.getConstraint();
        final Constraint        neg = ConstraintCombiner.makeNegation(constraint);

        return ConstraintCombiner.makeDisjunction(constraint, neg);
    }

    @Override
    public Iterable<Variable> getExpectedVariables()
    {
        final List<Variable> result = new ArrayList<Variable>();

        result.add(new Variable("x", BIT_VECTOR_TYPE.valueOf("0", 10)));

        return result;
    }
}