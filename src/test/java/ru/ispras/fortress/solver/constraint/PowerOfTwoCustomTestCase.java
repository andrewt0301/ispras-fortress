/*
 * Copyright (c) 2012 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * PowerOfTwoCustomTestCase.java, Oct 5, 2012 3:29:51 PM Andrei Tatarnikov
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
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.solver.Solver;
import ru.ispras.fortress.solver.SolverId;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintBuilder;
import ru.ispras.fortress.solver.constraint.ConstraintKind;
import ru.ispras.fortress.solver.constraint.Formulas;
import ru.ispras.fortress.solver.function.Function;

public class PowerOfTwoCustomTestCase extends GenericSolverSampleTestBase
{
    @Override
    public PowerOfTwoCustom createSample()
    {
        return new PowerOfTwoCustom();
    }

    /**
    The sample is similar to the PowerOfTwo sample, but the is_pow_of_two function 
    is provided as a custom text-based operation that extends the solver.
      
    The constraint as described in the SMT-LIB language:

    <pre>
    (declare-const x (_ BitVec 32))

    (define-fun is_pow_of_two((a (_ BitVec 32))) Bool (= (bvand a (bvsub a (_ bv1 32))) (_ bv0 32)))
    (assert (is_pow_of_two x))

    (assert (bvugt x (_ bv100 32)))
    (assert (bvult x (_ bv200 32)))

    (check-sat)
    (get-value (x))
    (exit)</pre>

    Expected output:
    <pre>
    sat ((x #x00000080))</pre>
    */

    public static class PowerOfTwoCustom implements ISampleConstraint
    {
        private static final int      BIT_VECTOR_SIZE = 32;
        private static final DataType BIT_VECTOR_TYPE = DataType.BIT_VECTOR(BIT_VECTOR_SIZE);

        public static enum EPowerOfTwoCustomOperation
        {
            ISPOWOFTWO
        }

        private void registerCustomOperations(Solver solver)
        {
            final Variable param = new Variable("a", BIT_VECTOR_TYPE);
            
            final Node body = new NodeOperation(
                StandardOperation.EQ,
                new NodeOperation(
                    StandardOperation.BVAND,
                    new NodeVariable(param), 
                    new NodeOperation(
                        StandardOperation.BVSUB,
                        new NodeVariable(param),
                        new NodeValue(BIT_VECTOR_TYPE.valueOf("1", 10))
                    )
                ),
                new NodeValue(BIT_VECTOR_TYPE.valueOf("0", 10))
            );

            solver.addCustomOperation(
                new Function(EPowerOfTwoCustomOperation.ISPOWOFTWO, DataType.BOOLEAN, body, param)
            );
        }

        public Constraint getConstraint()
        {
            final Solver solver = SolverId.Z3_TEXT.getSolver();
            assert null != solver;

            registerCustomOperations(solver);

            final ConstraintBuilder builder = new ConstraintBuilder();

            builder.setName("PowerOfTwoCustomText");
            builder.setKind(ConstraintKind.FORMULA_BASED);
            builder.setDescription("PowerOfTwoCustomText constraint");

            final NodeVariable x = new NodeVariable(builder.addVariable("x", BIT_VECTOR_TYPE));

            final Formulas formulas = new Formulas();
            builder.setInnerRep(formulas);

            formulas.add(
                new NodeOperation(
                    StandardOperation.BVUGT,
                    x,
                    new NodeValue(BIT_VECTOR_TYPE.valueOf("100", 10))
                )
            );

            formulas.add(
                new NodeOperation(
                    StandardOperation.BVULT,
                    x,
                    new NodeValue(BIT_VECTOR_TYPE.valueOf("200", 10))
                )
            );

            formulas.add(
                new NodeOperation(
                    EPowerOfTwoCustomOperation.ISPOWOFTWO,
                    x
                )
            );

            return builder.build();
        }

        public Iterable<Variable> getExpectedVariables()
        {
            final List<Variable> result = new ArrayList<Variable>();

            result.add(new Variable("x", BIT_VECTOR_TYPE.valueOf("128", 10)));

            return result;
        }
    }
}