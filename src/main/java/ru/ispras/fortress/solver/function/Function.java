/*
 * Copyright 2012-2014 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.solver.function;

import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.util.InvariantChecks;

/**
 * The Function class describes a custom function that extends the functionality of a solver. A
 * function represents an operation described in terms of expressions that use existing solver
 * operations.
 * 
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */

public final class Function {
  private final Enum<?> id;
  private final DataType returnType;
  private final Node body;
  private final Variable[] parameters;

  /**
   * Creates a function with a variable number of parameters.
   * 
   * @param id The identifier of the operator the function is associated with.
   * @param returnType The function return type.
   * @param body The body of the function (underlying expression).
   * @param parameters An variable-length list of parameters.
   * 
   * @throws IllegalArgumentException if any of the parameters is {@code null}.
   */

  public Function(
      final Enum<?> id,
      final DataType returnType,
      final Node body,
      final Variable... parameters) {
    InvariantChecks.checkNotNull(id);
    InvariantChecks.checkNotNull(returnType);
    InvariantChecks.checkNotNull(body);
    InvariantChecks.checkNotNull(parameters);

    this.id = id;
    this.returnType = returnType;
    this.body = body;
    this.parameters = parameters;
  }

  /**
   * Returns the identifier of the operation associated with the function.
   * 
   * @return Operation identifier for the function.
   */

  public Enum<?> getId() {
    return id;
  }

  /**
   * Returns a unique name for the function. The name is based on the function's identifier, return
   * value type and parameter types. It helps distinguish overloaded functions that use the same
   * identifier but have different parameter type and return types.
   * 
   * @return Unique name of the function.
   */

  public String getUniqueName() {
    final StringBuilder sb = new StringBuilder();

    sb.append(id.getClass().getSimpleName());
    sb.append('_');
    sb.append(id.name());

    sb.append("_RET_");
    sb.append(returnType.getTypeId());

    if (returnType.getSize() != 0) {
      sb.append(returnType.getSize());
    }

    if (parameters.length > 0) {
      sb.append("_PARAMS");
    }

    for (final Variable v : parameters) {
      final DataType type = v.getType();

      sb.append('_');
      sb.append(type.getTypeId());

      if (type.getSize() != 0) {
        sb.append(type.getSize());
      }
    }

    return sb.toString();
  }

  /**
   * Returns the function return type.
   * 
   * @return The function return type.
   */

  public DataType getReturnType() {
    return returnType;
  }

  /**
   * Returns the body of the function (underlying expression).
   * 
   * @return The syntax element describing the body of the function.
   */

  public Node getBody() {
    return body;
  }

  /**
   * Returns the parameter count.
   * 
   * @return The number of parameters.
   */

  public int getParameterCount() {
    return parameters.length;
  }

  /**
   * Returns function parameters by their index.
   * 
   * @param index The index of the needed parameter.
   * @return A function parameter.
   * 
   * @throws IndexOutOfBoundsException if the parameter index is out of bounds of the parameter
   *         array.
   */

  public Variable getParameter(final int index) {
    InvariantChecks.checkBounds(index, parameters.length);
    return parameters[index];
  }
}
