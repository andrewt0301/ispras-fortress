/*
 * Copyright 2015 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.calculator;

import ru.ispras.fortress.data.Data;

public abstract class CalculatorOperation<OperationId extends Enum<OperationId>> 
  implements Operation<OperationId> {

  private final OperationId id;
  private final ArityRange arity;

  public CalculatorOperation(OperationId id, ArityRange arity) {
    this.id = id;
    this.arity = arity;
  }

  public OperationId getOperationId() {
    return id;
  }

  public ArityRange getOperationArity() {
    return arity;
  }

  public boolean validTypes(Data... operands) {
    return OperationGroup.equalTypes(operands);
  }

  abstract public Data calculate(Data... operands);
}
