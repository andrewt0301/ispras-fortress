/*
 * Copyright 2014 ISP RAS (http://www.ispras.ru)
 * 
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 * 
 * http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software distributed under the License
 * is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
 * or implied. See the License for the specific language governing permissions and limitations under
 * the License.
 */

package ru.ispras.fortress.solver.constraint;

import java.util.ArrayList;
import java.util.List;

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.*;

/**
 * The constraint as described in pseudo language similar to SMT-LIB:
 * 
 * <pre>
 * (define-sort ARRAY_TYPE () (Array Int Int))
 * (declare-fun a () ARRAY_TYPE)
 * (declare-fun v () ARRAY_TYPE)
 * (assert (= a (store v 37 37)))
 * (assert (= a '((37 37))))
 * (check-sat)
 * (get-value (a))
 * (get-value (v))
 * (get-model)
 * (exit)
 * </pre>
 */

public class ArrayTestCase extends GenericSolverTestBase {
  public ArrayTestCase() {
    super(new ArrayInvariant());
  }
}


final class ArrayInvariant implements GenericSolverTestBase.SampleConstraint {
  private static final DataType ARRAY_TYPE = DataType.MAP(DataType.INTEGER, DataType.INTEGER);
  private static final String ARRAY_VALUE = "((37:37))";

  public Constraint getConstraint() {
    final ConstraintBuilder builder = new ConstraintBuilder();

    builder.setName("ArrayInvariant");
    builder.setKind(ConstraintKind.FORMULA_BASED);
    builder.setDescription("ArrayInvariant constraint");

    final NodeVariable a = new NodeVariable(builder.addVariable("a", ARRAY_TYPE));
    final NodeVariable v = new NodeVariable(builder.addVariable("v", ARRAY_TYPE));

    final NodeValue value = new NodeValue(DataType.INTEGER.valueOf("37", 10));
    final NodeValue array = new NodeValue(ARRAY_TYPE.valueOf(ARRAY_VALUE, 10));

    final Node stored = new NodeOperation(StandardOperation.STORE, v, value, value);

    final Formulas formulas = new Formulas();
    builder.setInnerRep(formulas);

    formulas.add(new NodeOperation(StandardOperation.EQ, a, stored));
    formulas.add(new NodeOperation(StandardOperation.EQ, a, array));

    return builder.build();
  }

  public Iterable<Variable> getExpectedVariables() {
    final List<Variable> result = new ArrayList<Variable>();

    result.add(new Variable("a", ARRAY_TYPE.valueOf(ARRAY_VALUE, 10)));
    result.add(new Variable("v", ARRAY_TYPE.valueOf("()", 10)));

    return result;
  }
}
