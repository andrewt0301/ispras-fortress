/*
 * Copyright 2014 ISP RAS (http://www.ispras.ru), UniTESK Lab (http://www.unitesk.com)
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
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

package ru.ispras.fortress.solver;

import java.util.ArrayList;
import java.util.List;

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.NodeExpr;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintBuilder;
import ru.ispras.fortress.solver.constraint.Formulas;

/**
 * @author <a href="mailto:ssedai@ispras.ru">Sergey Smolov</a>
 */

public class NoNameArithmeticTestCase extends GenericSolverSampleTestBase
{
    @Override
    public ISampleConstraint createSample()
    {
        return new NoNameArithmetic();
    }
    
    /** The constraint as described in the SMT language:

    <pre>
    (declare-const x Int)
    (assert (= x (+ 2 2)))
    (check-sat)
    (get-value (x))
    (exit)</pre>

    Expected output: 
    
    <pre>
    sat ((x 4))</pre>
    */

    public static class NoNameArithmetic implements ISampleConstraint
    {
        private static final DataType intType = DataType.INTEGER;

        @Override
        public Constraint getConstraint()
        {
            final ConstraintBuilder builder = new ConstraintBuilder();

            final NodeVariable x = new NodeVariable(builder.addVariable("x", intType));

            final Formulas formulas = new Formulas();
            builder.setInnerRep(formulas);

            formulas.add(
                new NodeExpr(
                    StandardOperation.EQ,
                    x,
                    new NodeExpr(
                        StandardOperation.ADD,
                        new NodeValue(intType.valueOf("2", 10)),
                        new NodeValue(intType.valueOf("2", 10))
                    )
                )
            );

            return builder.build();
        }

        @Override
        public Iterable<Variable> getExpectedVariables()
        {
            final List<Variable> result = new ArrayList<Variable>();

            result.add(new Variable("x", intType.valueOf("4", 10)));

            return result;
        }
    }
}
