/*
 * Copyright (c) 2014 ISPRAS (www.ispras.ru)
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * SolverUtils.java, Aug 22, 2014 2:36:30 PM Andrei Tatarnikov
 * 
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not
 * use this file except in compliance with the License. You may obtain a copy of
 * the License at
 * 
 * http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations under
 * the License.
 */

package ru.ispras.fortress.solver;

import java.util.EnumSet;
import java.util.Set;

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.expression.ExprTreeVisitor.Status;
import ru.ispras.fortress.expression.ExprTreeVisitorDefault;
import ru.ispras.fortress.expression.ExprTreeWalker;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintBuilder;
import ru.ispras.fortress.solver.constraint.ConstraintKind;
import ru.ispras.fortress.solver.constraint.Formulas;

public final class SolverUtils
{
    private SolverUtils() {}

    public static boolean isCondition(Node expr)
    {
        if (null == expr)
            throw new NullPointerException();

        return expr.getDataType().equals(DataType.BOOLEAN);
    }
    
    public static boolean isAtomicCondition(Node expr)
    {
        if (!isCondition(expr))
            return false;

        final Set<StandardOperation> logicOperations = EnumSet.of(
            StandardOperation.AND,
            StandardOperation.OR,
            StandardOperation.NOT,
            StandardOperation.XOR,
            StandardOperation.IMPL
        );

        final ExprTreeVisitorDefault visitor = new ExprTreeVisitorDefault()
        {
            @Override public void onOperationBegin(NodeOperation node)
            {
                if (logicOperations.contains(node.getOperationId()))
                    setStatus(Status.ABORT);
            }
        };

        final ExprTreeWalker walker = new ExprTreeWalker(visitor);
        walker.visit(expr);

        return visitor.getStatus() == Status.OK;
    }

    public static Node getConjunction(Node ... exprs)
    {
        checkNotEmpty(exprs);
        checkAllConditions(exprs);

        return new NodeOperation(StandardOperation.AND, exprs);
    }
    
    public static Node getDisjunction(Node ... exprs)
    {
        checkNotEmpty(exprs);
        checkAllConditions(exprs);

        return new NodeOperation(StandardOperation.OR, exprs);
    }

    public static Node getNegation(Node ... exprs)
    {
        return new NodeOperation(StandardOperation.NOT, getConjunction(exprs));
    }

    public static Node getComplement(Node ... exprs)
    {
        return new NodeOperation(StandardOperation.NOT, getDisjunction(exprs));
    }

    public static boolean areComplete(Node ... exprs)
    {
        final Node target = 
            new NodeOperation(StandardOperation.NOT, getComplement(exprs));
        
        return isSAT(target);
    }

    public static boolean areCompatible(Node ... exprs)
    {
        final Node target = getConjunction(exprs);

        return isSAT(target);
    }
    
    private static boolean isSAT(Node assertion)
    {
        final ConstraintBuilder builder = 
             new ConstraintBuilder(ConstraintKind.FORMULA_BASED);

        final Formulas formulas = new Formulas(assertion);
        builder.setInnerRep(formulas);

        builder.addVariables(formulas.getVariables());
        final Constraint constraint = builder.build();

        final Solver solver = constraint.getKind().getDefaultSolverId().getSolver();
        final SolverResult solverResult = solver.solve(constraint);

        return SolverResult.Status.SAT == solverResult.getStatus();
    }

    private static void checkNotEmpty(Node ... exprs)
    {
        if (0 == exprs.length)
            throw new IllegalArgumentException("No expressions are provided.");
    }

    private static void checkAllConditions(Node ... exprs)
    {
        for (Node expr : exprs)
            if (!isCondition(expr))
                throw new IllegalArgumentException(
                     "Expression is not a condition: " + expr.toString());
    }
}
