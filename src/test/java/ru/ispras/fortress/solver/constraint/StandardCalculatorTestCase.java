/*
 * Copyright (c) 2013 ISPRAS (www.ispras.ru)
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * StandardCalculatorTestCase.java, Jul 2, 2013 5:42:36 PM Andrei Tatarnikov
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

package ru.ispras.fortress.solver.constraint;

import java.util.ArrayList;
import java.util.List;

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.transformer.ReduceOptions;
import ru.ispras.fortress.transformer.Transformer;

public class StandardCalculatorTestCase extends GenericSolverTestBase
{
    public StandardCalculatorTestCase()
    {
        super(new StandardCalculator());
    }

    /** The constraint as described in the SMT language:

    <pre>
    (declare-const a Int)
    (declare-const b Int)
    (declare-const c Int)
    (declare-const d Int)
    (declare-const e Int)
    (declare-const f Int)

    (assert (= a (+ 2 3)))
    (assert (= b (- 10 6)))
    (assert (= c (* 2 5)))
    (assert (= d (div 12 5)))
    (assert (= e (rem 10 3)))
    (assert (= f (mod 10 3)))

    (check-sat)
    (get-value (a b c d e f))</pre>

    Expected output:

    sat ((a 5) (b 4) (c 10) (d 2) (e 1) (f 1))
    */

    public static class StandardCalculator implements SampleConstraint
    {
        private static final DataType intType = DataType.INTEGER;

        @Override
        public Constraint getConstraint()
        {
            final ConstraintBuilder builder = new ConstraintBuilder();

            builder.setName("StandardCalculator");
            builder.setKind(ConstraintKind.FORMULA_BASED);
            builder.setDescription("Expression reduction with the standard expression calculator.");

            final NodeVariable a = new NodeVariable(builder.addVariable("a", intType));
            final NodeVariable b = new NodeVariable(builder.addVariable("b", intType));
            final NodeVariable c = new NodeVariable(builder.addVariable("c", intType));
            final NodeVariable d = new NodeVariable(builder.addVariable("d", intType));
            final NodeVariable e = new NodeVariable(builder.addVariable("e", intType));
            final NodeVariable f = new NodeVariable(builder.addVariable("f", intType));

            final Formulas formulas = new Formulas();
            builder.setInnerRep(formulas);

            formulas.add(
                new NodeOperation(
                    StandardOperation.EQ,
                    a,
                    Transformer.reduce(
                        ReduceOptions.NEW_INSTANCE,
                        new NodeOperation(
                            StandardOperation.ADD,
                            new NodeValue(intType.valueOf("2", 10)),
                            new NodeValue(intType.valueOf("3", 10))
                        )
                    )
                )
            );

            formulas.add(
                new NodeOperation(
                    StandardOperation.EQ,
                    b, 
                    Transformer.reduce(
                        ReduceOptions.NEW_INSTANCE,
                        new NodeOperation(
                            StandardOperation.SUB,
                            new NodeValue(intType.valueOf("10", 10)),
                            new NodeValue(intType.valueOf("6", 10))
                        )
                    )
                )
            );

            formulas.add(
                new NodeOperation(
                    StandardOperation.EQ,
                    c, 
                    Transformer.reduce(
                        ReduceOptions.NEW_INSTANCE,
                        new NodeOperation(
                            StandardOperation.MUL,
                            new NodeValue(intType.valueOf("2", 10)),
                            new NodeValue(intType.valueOf("5", 10))
                        )
                    )
                )
            );

            formulas.add(
                new NodeOperation(
                    StandardOperation.EQ,
                    d,
                    Transformer.reduce(
                        ReduceOptions.NEW_INSTANCE,
                        new NodeOperation(
                            StandardOperation.DIV,
                            new NodeValue(intType.valueOf("12", 10)),
                            new NodeValue(intType.valueOf("5", 10))
                        )
                    )
                )
            );

            formulas.add(
                new NodeOperation(
                    StandardOperation.EQ,
                    e,
                    Transformer.reduce(
                        ReduceOptions.NEW_INSTANCE,
                        new NodeOperation(
                            StandardOperation.REM,
                            new NodeValue(intType.valueOf("10", 10)),
                            new NodeValue(intType.valueOf("3", 10))
                        )
                    )
                )
            );

            formulas.add(
                new NodeOperation(
                    StandardOperation.EQ,
                    f,
                    Transformer.reduce(
                        ReduceOptions.NEW_INSTANCE,
                        new NodeOperation(
                            StandardOperation.MOD,
                            new NodeValue(intType.valueOf("10", 10)),
                            new NodeValue(intType.valueOf("3", 10))
                        )
                    )
                )
            );

            return builder.build();
        }

        @Override
        public Iterable<Variable> getExpectedVariables()
        {
            final List<Variable> result = new ArrayList<Variable>();

            result.add(new Variable("a", intType.valueOf("5", 10)));
            result.add(new Variable("b", intType.valueOf("4", 10)));
            result.add(new Variable("c", intType.valueOf("10", 10)));
            result.add(new Variable("d", intType.valueOf("2", 10)));
            result.add(new Variable("e", intType.valueOf("1", 10)));
            result.add(new Variable("f", intType.valueOf("1", 10)));

            return result;
        }
    }
}
