/*
 * Copyright (c) 2013 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * ConstraintCombiner.java, Nov 25, 2013 4:30:38 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver.constraint;

import ru.ispras.fortress.expression.Node;

/**
 * The ConstraintCombiner class provides methods to create new constraints by combining
 * existing ones (by performing negation, logical conjunction and logical disjunction).
 * 
 * @author Andrei Tatarnikov
 */

public final class ConstraintCombiner
{
    private static final String DISJUNCTION = "Disjunction of '%s' and '%s'";
    private static final String CONJUNCTION = "Conjunction of '%s' and '%s'";
    private static final String   NEGATION  = "Negation of '%s'";

    private ConstraintCombiner() {}

    /**
     * Creates a new constraint by performing logical negation on the specified constraint.
     * 
     * @param a A constraint object.
     * @return A new constraint object.
     * 
     * @throws NullPointerException if the parameter equals null.
     * @throws IllegalArgumentException if the parameter is not a formula-based
     * constraint (its type is not ConstraintKind.FORMULA_BASED).  
     */

    public static Constraint makeNegation(Constraint a)
    {
        formulaBasedCheck(a);

        final String name = String.format(NEGATION, a.getName());
        final ConstraintBuilder builder = new ConstraintBuilder(name, a.getKind());

        final Formulas formulas = new Formulas();
        builder.setInnerRep(formulas);

        final Node sourceExpr = ((Formulas) a.getInnerRep()).asSingleExpr();
        formulas.add(Node.NOT(sourceExpr));

        builder.addVariableCopies(a.getVariables());
        return builder.build();
    }

    /**
     * Creates a new constraint by performing logical conjunction on the specified constraints.
     * 
     * @param a A constraint object.
     * @param b A constraint object.
     * @return A new constraint object.
     * 
     * @throws NullPointerException if any of the parameters equals null.
     * @throws IllegalArgumentException if any of the parameters is not a formula-based
     * constraint (its type is not ConstraintKind.FORMULA_BASED).
     */

    public static Constraint makeConjunction(Constraint a, Constraint b)
    {
        formulaBasedCheck(a);
        formulaBasedCheck(b);

        final String name = String.format(CONJUNCTION, a.getName(), b.getName());
        final ConstraintBuilder builder = new ConstraintBuilder(name, a.getKind());

        final Formulas formulas = new Formulas();
        builder.setInnerRep(formulas);

        formulas.addAll((Formulas) a.getInnerRep());
        formulas.addAll((Formulas) b.getInnerRep());

        builder.addVariableCopies(a.getVariables());
        builder.addVariableCopies(b.getVariables());

        return builder.build();
    }

    /**
     * Creates a new constraint by performing logical disjunction on the specified constraints.
     * 
     * @param a A constraint object.
     * @param b A constraint object.
     * @return A new constraint object.
     * 
     * @throws NullPointerException if any of the parameters equals null.
     * @throws IllegalArgumentException if any of the parameters is not a formula-based
     * constraint (its type is not ConstraintKind.FORMULA_BASED).
     */

    public static Constraint makeDisjunction(Constraint a, Constraint b)
    {
        formulaBasedCheck(a);
        formulaBasedCheck(b);

        final String name = String.format(DISJUNCTION, a.getName(), b.getName());
        final ConstraintBuilder builder = new ConstraintBuilder(name, a.getKind());

        final Formulas formulas = new Formulas();
        builder.setInnerRep(formulas);

        final Node sourceExprA = ((Formulas) a.getInnerRep()).asSingleExpr();
        final Node sourceExprB = ((Formulas) b.getInnerRep()).asSingleExpr();
        formulas.add(Node.OR(sourceExprA, sourceExprB));

        builder.addVariableCopies(a.getVariables());
        builder.addVariableCopies(b.getVariables());

        return builder.build();
    }

    private static void formulaBasedCheck(Constraint c)
    {
        if (null == c)
            throw new NullPointerException();

        if (ConstraintKind.FORMULA_BASED != c.getKind())
            throw new IllegalArgumentException(
                String.format("The %s constraint is not formula based.", c.getName()));
    }
}
