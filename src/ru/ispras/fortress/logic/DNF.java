/*
 * Copyright 2014 Institute for System Programming of RAS (http://www.ispras.ru)
 *
 * Licensed under the Apache License, Version 2.0 (the "License")
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package ru.ispras.fortress.logic;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Set;

/**
 * This class contains a set of utils dealing with disjunctive normal forms.
 *
 * @author <a href="mailto:kamkin@ispras.ru">Alexander Kamkin</a>
 */ 
public final class DNF
{
    /**
     * Checks whether two clauses (conjuncts), <code>lhs</code> and <code>rhs</code>,
     * are disjoint (mutually exclusive or orthogonal).
     *
     * @param lhs the left-hand-side clause.
     * @param rhs the right-hand-side clause.
     * @return true iff the clauses are disjoint.
     */
    public static boolean areDisjoint(final Clause lhs, final Clause rhs)
    {
        final Set<Integer> common = lhs.getCommonVars(rhs);

        // Iterate over all common variables.
        for(final int var: common)
        {
            // For each of them check whether it occurs with different signs.
            if(lhs.getSign(var) != rhs.getSign(var))
                { return true; }
        }
        
        return false;
    }

    /**
     * Splits one of the clauses, <code>lhs</code> or <code>rhs</code>, so as
     * to make them disjoint.
     *
     * @return the index of the index clause or -1 if no one has been index.
     */
    private static int orthogonalize(final Clause lhs, final Clause rhs, NormalForm LHS, NormalForm RHS)
    {
        // The specified clauses are disjoint.
        if(areDisjoint(lhs, rhs))
        {
            // They are added to the corresponding normal forms without changes.
            LHS.add(lhs);
            RHS.add(rhs);
            return -1;
        }

        // Try to split the right-hand-side clause (#1).
        int index = 1;
        // To do it, the left-hand-side clause should have unique variables.
        Set<Integer> unique = lhs.getUniqueVars(rhs);

        // If it does not.
        if(unique.isEmpty())
        {
            // Try to split the left-hand-side clause (#0).
            index = 0;
            // To do it, the right-hand-side clause should have unique variables.
            unique = rhs.getUniqueVars(lhs);

            // If it does not, the clauses are equal.
            if(unique.isEmpty())
            {
                // The right-hand-side clause is removed (#1).
                LHS.add(lhs);
                return 1;
            }
        }

        // The clauses are neither equal nor disjoint.
        final Clause fixed = (index == 1 ? lhs : rhs);
        final Clause split = (index == 1 ? rhs : lhs);
        NormalForm   FIXED = (index == 1 ? LHS : RHS);
        NormalForm   SPLIT = (index == 1 ? RHS : LHS);
        
        // One of the clauses is fixed (the other one is split).
        FIXED.add(fixed);

        int     prev = -1;
        boolean sign = false;

        // Additional literals to be added to the splitting clause.
        Clause factor = new Clause();

        // Iterate over the unique variables of the fixed clause.
        for(final int var: unique)
        {
            // One of the new clauses to be added.
            Clause clause = new Clause(split);
            
            if(prev != -1) { factor.add(prev, sign); }

            factor.add((prev = var), !(sign = fixed.getSign(var)));
            clause.add(factor);
            SPLIT.add(clause);
        }

        // Return the index of the split clause.
        return index;
    }

    /**
     * Replaces the i-th clause of the list with the specified set of clauses.
     *
     * @param clauses the list of clauses.
     * @param i the index of the clause to be replaced.
     * @param form the set of clauses to be substituted.
     */
    private static void replace(List<Clause> clauses, int i, final NormalForm form)
    {
        if(form.isEmpty())
        {
            clauses.remove(i);
            return;
        }

        final List<Clause> list = form.getClauses();
        
        if(form.size() == 1)
        {
            clauses.set(i, list.get(0));
            return;
        }
        
        clauses.set(i, list.get(list.size() - 1));
        clauses.addAll(i, list.subList(0, list.size() - 1));
    }
    
    public static NormalForm orthogonalize(final NormalForm form)
    {
        ArrayList<Clause> clauses = new ArrayList<Clause>(form.getClauses());

        for(int i = 1; i < clauses.size(); i++)
        for(int j = 0; j < i; j++)
        {
            NormalForm LHS = new NormalForm(NormalForm.Type.DNF);
            NormalForm RHS = new NormalForm(NormalForm.Type.DNF);

            // Split one of the clauses to make them disjoint.
            int index = orthogonalize(clauses.get(j), clauses.get(i), LHS, RHS);

            // The left-hand-side clause is rewritten (#0).
            if(index == 0)
            {
                replace(clauses, j, LHS);
                
                i += (LHS.size() - 1);
                j += (LHS.size() - 1);
            }
            // The right-hand-side clause is rewritten (#1).
            else if(index == 1)
            {
                replace(clauses, i, RHS);
                
                if(RHS.isEmpty())
                    { j = (i >= clauses.size() ? i : -1); }
            }
        }

        return new NormalForm(NormalForm.Type.DNF, clauses);
    }

    private static void replace(ArrayList<Clause> clauses, HashMap<Integer, Integer> branches, int pre_i, int i, final NormalForm form)
    {
        if(form.isEmpty())
        {
            branches.put(pre_i, next(branches, i));
            return;
        }

        final List<Clause> list = form.getClauses();

        if(form.size() == 1)
        {
            clauses.set(i, list.get(0));
            return;
        }

        int return_i = next(branches, i);
        int branch_i = clauses.size();

        clauses.set(i, list.get(0));
        clauses.addAll(list.subList(1, list.size()));

        branches.put(i, branch_i);
        branches.put(clauses.size() - 1, return_i);
    }
    
    private static int next(final HashMap<Integer, Integer> branches, int i)
    {
        if(i == -1) { return 0; }

        final Integer j = branches.get(i);
        return (j == null ? i + 1 : j);
    }

    private static NormalForm construct(final HashMap<Integer, Integer> branches, final ArrayList<Clause> clauses)
    {
        NormalForm form = new NormalForm(NormalForm.Type.DNF);

        for(int i = 0; i != -1; i = next(branches, i))
            { form.add(clauses.get(i)); }
            
        return form;
    }

    public static NormalForm orthogonalize1(final NormalForm form)
    {
        ArrayList<Clause> clauses = new ArrayList<Clause>(form.getClauses());
        clauses.ensureCapacity(2 * clauses.size());

        if(clauses.isEmpty())
            { return new NormalForm(NormalForm.Type.DNF); }

        HashMap<Integer, Integer> branches = new HashMap<Integer, Integer>(2 * clauses.size());
        branches.put(clauses.size() - 1, -1);
        
        for(int pre_i, i = next(branches, pre_i =  0); i != -1; i = next(branches, pre_i = i))
        for(int pre_j, j = next(branches, pre_j = -1); j !=  i; j = next(branches, pre_j = j))
        {
            //System.out.println(pre_i + " " + i + " " + pre_j + " " + j);
            NormalForm LHS = new NormalForm(NormalForm.Type.DNF);
            NormalForm RHS = new NormalForm(NormalForm.Type.DNF);

            // Split one of the clauses to make them disjoint.
            int index = orthogonalize(clauses.get(j), clauses.get(i), LHS, RHS);

            // The left-hand-side clause is rewritten (#0).
            if(index == 0)
            {
                replace(clauses, branches, pre_j, j, LHS);
                if(LHS.isEmpty()) { j = pre_j; }
            }
            // The right-hand-side clause is rewritten (#1).
            else if(index == 1)
            {
                replace(clauses, branches, pre_i, i, RHS);
                if(RHS.isEmpty()) { i = pre_i; break; }
            }
        }
        
        return construct(branches, clauses);
    }
}
