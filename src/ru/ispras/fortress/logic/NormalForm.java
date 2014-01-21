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

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

public final class NormalForm
{
    /**
     * This enumeration contains the type of the normal form.
     */
    public enum Type
    {
        /// Disjunctive normal form.
        DNF,
        /// Conjunctive normal form.
        CNF
    }

    /// The type of the form.
    private Type type;
    /// Constains the clauses of the form.
    private List<Clause> clauses;

    /**
     * Constructs the empty form of the specified type.
     */
    public NormalForm(Type type)
    {
        this.type = type;
        this.clauses = new LinkedList<Clause>();
    }
    
    /**
     * Constructs the empty form of the specified type.
     */
    public NormalForm(Type type, Collection<Clause> clauses)
    {
        this.type = type;
        this.clauses = new LinkedList<Clause>(clauses);
    }

    public Type getType()
    {
        return type;
    }
    
    public boolean isEmpty()
    {
        return clauses.isEmpty();
    }
    
    public int size()
    {
        return clauses.size();
    }

    public List<Clause> getClauses()
    {
        return clauses;
    }
    
    public void add(final Clause clause)
    {
        clauses.add(clause);
    }
    
    public void add(final NormalForm form)
    {
        clauses.addAll(form.clauses);
    }
    
    public void clear()
    {
        clauses.clear();
    }
    
    public String toString()
    {
        final String neg_op = "~";
        final String ext_op = type == Type.DNF ? " | " : " & ";
        final String int_op = type == Type.DNF ? " & " : " | ";

        StringBuffer buffer = new StringBuffer();
        
        boolean ext_sign = false;
        for(final Clause clause: clauses)
        {
            if(ext_sign) { buffer.append(ext_op); }
            ext_sign = true;
        
            buffer.append("(");
            {
                boolean int_sign = false;
                for(int var: clause.getVars())
                {
                    if(int_sign) { buffer.append(int_op); }
                    int_sign = true;
                
                    buffer.append(clause.getSign(var) ? "~" : "");
                    buffer.append("x" + var);
                }
            }
            buffer.append(")");
        }
        
        return buffer.toString();
    }
}