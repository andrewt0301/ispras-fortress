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
import java.util.List;
import java.util.Set;

public class DNF
{
    public static boolean areDisjoint(final Clause lhs, final Clause rhs)
    {
        final Set<Integer> common = lhs.getCommonVars(rhs);

        for(final int var: common)
        {
            if(lhs.getSign(var) != rhs.getSign(var))
                { return true; }
        }
        
        return false;
    }

    public static int orthogonalize(final Clause lhs, final Clause rhs, NormalForm lnf, NormalForm rhf)
    {
        NormalForm result = new NormalForm(NormalForm.Type.DNF);

        // The clauses are disjoint (orthogonal).
        if(areDisjoint(lhs, rhs))
        {
            lnf.add(lhs); // TODO: do not copy if unchanged
            rhf.add(rhs);
            return -1;
        }

        int split = 1;
        Set<Integer> vars = lhs.getUniqueVars(rhs);

        if(vars.isEmpty())
        {
            split = 0;
            vars = rhs.getUniqueVars(lhs);

            // The clauses are equal.
            if(vars.isEmpty())
            {
                lhs.add(new Clause(lhs));
                return 1;
            }
        }

        // The clauses are neither equal nor disjoint.
        final Clause x = split == 1 ? lhs : rhs;
        final Clause y = split == 1 ? rhs : lhs;
        
        NormalForm a = split == 1 ? lnf : rhf;
        NormalForm b = split == 1 ? rhf : lnf;
        
        // The x clause stays unchanged.
        a.add(x);

        Clause factor = new Clause();
            
        int v = -1;
        boolean s = false;

        // The y clause is split.
        for(final int var: vars)
        {
            Clause z = new Clause(y);
            
            if(v != -1)
                { factor.add(v, s); }

            factor.add((v = var), !(s = x.getSign(var)));
            z.add(factor);
            
            b.add(z);
        }
        
        return split;
    }

    private static void replace(List<Clause> clauses, int i, final NormalForm form)
    {
        if(form.size() == 1)
        {
            final Clause clause = form.getClauses().get(0);
            clauses.set(i, clause);
        }
        else
        {
            clauses.remove(i);
            clauses.addAll(i, form.getClauses());
        }
    }
    
    public static NormalForm orthogonalize(final NormalForm form)
    {
        ArrayList<Clause> clauses = new ArrayList<Clause>(form.getClauses());

        for(int i = 1; i < clauses.size(); i++)
        for(int j = 0; j < i; j++)
        {
            NormalForm a = new NormalForm(NormalForm.Type.DNF);
            NormalForm b = new NormalForm(NormalForm.Type.DNF);

            int target = orthogonalize(clauses.get(j), clauses.get(i), a, b);

            // The left clause is rewritten.
            if(target == 0)
            {
                replace(clauses, j, a);
                
                i += (a.size() - 1);
                j += (a.size() - 1);
            }
            else if(target == 1)
            {
                replace(clauses, i, b);
                
                if(b.isEmpty())
                    { j = -1; }
            }
        }

        return new NormalForm(NormalForm.Type.DNF, clauses);
    }
}
