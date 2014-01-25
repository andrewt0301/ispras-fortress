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
import java.util.Collection;
import java.util.List;

/**
 * This class represents a normal form, which is a set of clauses.
 * The representation can be interpreted as either DNF or CNF.
 *
 * @author <a href="mailto:kamkin@ispras.ru">Alexander Kamkin</a>
 */ 
public final class NormalForm
{
    /**
     * This enumeration contains the type of the normal form.
     */
    public enum Type
    {
        /// Disjunctive normal form (DNF).
        DNF,
        /// Conjunctive normal form (CNF).
        CNF
    }

    /// The type of the normal form.
    private Type type;
    /// Constains the clauses of the normal form.
    private List<Clause> clauses;

    /**
     * Constructs the empty normal form of the specified type.
     *
     * @param type the type of the form.
     */
    public NormalForm(Type type)
    {
        this.type = type;
        this.clauses = new ArrayList<Clause>();
    }
    
    /**
     * Constructs the normal form of the specified type consisting of the
     * specified clauses.
     *
     * @param type the type of the form.
     * @param clauses the clauses of the form.
     */
    public NormalForm(Type type, Collection<Clause> clauses)
    {
        this.type = type;
        this.clauses = new ArrayList<Clause>(clauses);
    }

    /**
     * Returns the type of the normal form (<code>DNF</code> or <code>CNF</code>).
     *
     * @return the type of the form.
     */
    public Type getType()
    {
        return type;
    }

    /**
     * Checks whether the normal form is empty.
     *
     * @return true iff the form is empty.
     */
    public boolean isEmpty()
    {
        return clauses.isEmpty();
    }

    /**
     * Returns the number of clauses in the normal form.
     *
     * @return the size of the form.
     */
    public int size()
    {
        return clauses.size();
    }

    /**
     * Returns the clauses of the normal form.
     *
     * @return the clauses of the form.
     */
    public List<Clause> getClauses()
    {
        return clauses;
    }

    /**
     * Appends the specified clause to the normal form.
     *
     * @param clause the clause to be added.
     */
    public void add(final Clause clause)
    {
        clauses.add(clause);
    }
    
    /**
     * Appends the clauses of the normal form specified as a parameter to this
     * normal form.
     *
     * @param form the form whose clauses to be added.
     */
    public void add(final NormalForm form)
    {
        clauses.addAll(form.clauses);
    }

    /**
     * Removes all clauses of the normal form.
     */
    public void clear()
    {
        clauses.clear();
    }

    /**
     * Returns the string representation of the normal form.
     *
     * @return the string representing the form.
     */
    public String toString()
    {
        // final String neg_op = "~"; // andrewt >> unused local constraint 
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
