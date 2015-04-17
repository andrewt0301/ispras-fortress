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

import java.util.List;

public class CompositeCalculator implements CalculatorEngine {
  private final List<CalculatorEngine> engines;

  public CompositeCalculator(List<CalculatorEngine> engines) {
    this.engines = engines;
  }

  @Override
  public boolean isSupported(Enum<?> opId, Data... operands) {
    return findSupporting(opId, operands) != null;
  }

  @Override
  public Data calculate(Enum<?> opId, Data... operands) {
    final CalculatorEngine engine = findSupporting(opId, operands);
    if (engine != null) {
      return engine.calculate(opId, operands);
    }
    return null;
  }

  private CalculatorEngine findSupporting(Enum<?> opId, Data... operands) {
    for (CalculatorEngine engine : engines) {
      if (engine.isSupported(opId, operands)) {
        return engine;
      }
    }
    return null;
  }
}
