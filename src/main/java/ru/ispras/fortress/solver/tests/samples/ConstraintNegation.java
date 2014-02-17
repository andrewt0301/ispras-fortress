package ru.ispras.fortress.solver.tests.samples;

import java.util.ArrayList;
import java.util.List;


import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.*;
import ru.ispras.fortress.solver.constraint.*;

public class ConstraintNegation extends BVUGTOperation
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
            new NodeExpr(
                StandardOperation.NOT,
                new NodeExpr(
                    StandardOperation.EQ,
                    formula,
                    new NodeExpr(
                        StandardOperation.NOT,
                        negFormula
                    )
                )
            )
        );

        // (not(a) and a)
        formulas.add(
            new NodeExpr(
                StandardOperation.AND,
                negFormula,
                formula
            )
        );

        // not((not(a)) or a)
        formulas.add(
            new NodeExpr(
                StandardOperation.NOT,
                new NodeExpr(
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
