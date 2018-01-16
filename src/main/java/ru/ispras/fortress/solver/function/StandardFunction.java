/*
 * Copyright 2013-2018 ISP RAS (http://www.ispras.ru)
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
import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.util.InvariantChecks;

/**
 * The StandardFunction enumeration describes function templates describing functions that perform
 * the job of corresponding standard operations (see {@link StandardOperation}).
 * 
 * @author Andrei Tatarnikov
 */

public enum StandardFunction implements FunctionTemplate {
  /**
   * The items below are function templates for operations from the "Logic Arithmetic" group.
   */

  /** Group: Logic, Operation: Absolute value */
  ABS(StandardOperation.ABS, 1) {
    @Override
    protected Function newFunction(final DataType[] argTypes) {
      return StandardFunctionFactory.makeAbs(getId(), argTypes[0]);
    }
  },

  /** Group: Logic, Operation: Minimum */
  MIN(StandardOperation.MIN, 2) {
    @Override
    protected Function newFunction(final DataType[] argTypes) {
      return StandardFunctionFactory.makeMin(getId(), argTypes[0], argTypes[1]);
    }
  },

  /** Group: Logic, Operation: Maximum */
  MAX(StandardOperation.MAX, 2) {
    @Override
    protected Function newFunction(final DataType[] argTypes) {
      return StandardFunctionFactory.makeMax(getId(), argTypes[0], argTypes[1]);
    }
  },

  /**
   * The items below are function templates for operations from the
   * "Bit Vector Reduction Operations" group.
   * 
   * Operation semantics:
   * 
   * <pre>
   * From IEEE Standard for Verilog Hardware Description Language:
   * 
   * The unary reduction operators shall perform a bitwise operation on a single operand
   * to produce a single-bit result. For reduction and, reduction or, and reduction xor operators,
   * the first step of the operation shall apply the operator between the first bit of the operand
   * and the second. The second and subsequent steps shall apply the operator between the 1-bit
   * result of the prior step and the next bit of the operand using the same logic table. For
   * reduction nand, reduction nor, and reduction xnor operators, the result shall be computed by
   * inverting the result of the reduction and, reduction or, and reduction xor operation,
   * respectively.
   * 
   * See the manual for details.
   * </pre>
   */

  /** Group: Bit Vector Reduction, Operation: Reduction AND ({@literal &}) */
  BVANDR(StandardOperation.BVANDR, 1) {
    @Override
    protected Function newFunction(final DataType[] argTypes) {
      return StandardFunctionFactory.makeBVANDR(getId(), argTypes[0]);
    }
  },

  /** Group: Bit Vector Reduction, Operation: Reduction NAND ({@literal ~&}) */
  BVNANDR(StandardOperation.BVNANDR, 1) {
    @Override
    protected Function newFunction(final DataType[] argTypes) {
      return StandardFunctionFactory.makeBVNANDR(getId(), argTypes[0]);
    }
  },

  /** Group: Bit Vector Reduction, Operation: Reduction OR (|) */
  BVORR(StandardOperation.BVORR, 1) {
    @Override
    protected Function newFunction(final DataType[] argTypes) {
      return StandardFunctionFactory.makeBVORR(getId(), argTypes[0]);
    }
  },

  /** Group: Bit Vector Reduction, Operation: Reduction NOR (~|) */
  BVNORR(StandardOperation.BVNORR, 1) {
    @Override
    protected Function newFunction(final DataType[] argTypes) {
      return StandardFunctionFactory.makeBVNORR(getId(), argTypes[0]);
    }
  },

  /** Group: Bit Vector Reduction, Operation: Reduction XOR (^) */
  BVXORR(StandardOperation.BVXORR, 1) {
    @Override
    protected Function newFunction(final DataType[] argTypes) {
      return StandardFunctionFactory.makeBVXORR(getId(), argTypes[0]);
    }
  },

  /** Group: Bit Vector Reduction, Operation: Reduction XNOR (~^) */
  BVXNORR(StandardOperation.BVXNORR, 1) {
    @Override
    protected Function newFunction(final DataType[] argTypes) {
      return StandardFunctionFactory.makeBVXNORR(getId(), argTypes[0]);
    }
  };

  private final Enum<?> id;
  private final int argCount;

  private StandardFunction(final Enum<?> id, final int argCount) {
    this.id = id;
    this.argCount = argCount;
  }

  @Override
  public final Enum<?> getId() {
    return id;
  }

  public final int getArgumentCount() {
    return argCount;
  }

  @Override
  public final Function instantiate(final DataType[] argTypes) {
    InvariantChecks.checkNotNull(argTypes);

    if (argTypes.length != argCount) {
      throw new IllegalArgumentException(String.format(
        "Wrong number of arguments: %d, expected: %d.", argTypes.length, argCount));
    }

    return newFunction(argTypes);
  }

  protected abstract Function newFunction(DataType[] argTypes);
}
