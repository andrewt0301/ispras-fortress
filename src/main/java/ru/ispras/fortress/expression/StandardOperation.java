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

package ru.ispras.fortress.expression;

import ru.ispras.fortress.data.DataType;

/**
 * The StandardOperation.java enumeration contains identifiers that specify particular operations
 * used in expressions.
 * 
 * @author Andrei Tatarnikov
 */

public enum StandardOperation implements TypeRule {
  /**
   * The items below belong to the "Logic Operations" group.
   */

  /** Group: Logic, Operation: Equality */
  EQ(TypeRules.BOOLEAN),

  /** Group: Logic, Operation: Not Equal */
  NOTEQ(TypeRules.BOOLEAN),

  /** Group: Logic, Operation: Case equality */
  EQCASE(TypeRules.BOOLEAN),

  /** Group: Logic, Operation: Case not equality */
  NOTEQCASE(TypeRules.BOOLEAN),

  /** Group: Logic, Operation: AND */
  AND(TypeRules.BOOLEAN),

  /** Group: Logic, Operation: OR */
  OR(TypeRules.BOOLEAN),

  /** Group: Logic, Operation: NOT */
  NOT(TypeRules.BOOLEAN),

  /** Group: Logic, Operation: XOR */
  XOR(TypeRules.BOOLEAN),

  /** Group: Logic, Operation: Implication */
  IMPL(TypeRules.BOOLEAN),

  /** Group: Logic, Operation: Conditional expression aka if-then-else */
  ITE(TypeRules.ITE),

  /**
   * The items below belong to the "Logic Arithmetic" group.
   */

  /** Group: Logic, Operation: Unary minus */
  MINUS(TypeRules.FIRST_KNOWN_NUM_ARG),

  /** Group: Logic, Operation: Unary plus */
  PLUS(TypeRules.FIRST_KNOWN_NUM_ARG),

  /** Group: Logic, Operation: Addition */
  ADD(TypeRules.FIRST_KNOWN_NUM_ARG),

  /** Group: Logic, Operation: Subtraction */
  SUB(TypeRules.FIRST_KNOWN_NUM_ARG),

  /** Group: Logic, Operation: Division */
  DIV(TypeRules.FIRST_KNOWN_NUM_ARG),

  /** Group: Logic, Operation: Multiplication */
  MUL(TypeRules.FIRST_KNOWN_NUM_ARG),

  /** Group: Logic, Operation: Remainder */
  REM(TypeRules.FIRST_KNOWN_NUM_ARG),

  /** Group: Logic, Operation: Modulo */
  MOD(TypeRules.FIRST_KNOWN_NUM_ARG),

  /** Group: Logic, Operation: Less */
  LESS(TypeRules.BOOLEAN),

  /** Group: Logic, Operation: Less or equal */
  LESSEQ(TypeRules.BOOLEAN),

  /** Group: Logic, Operation: Greater */
  GREATER(TypeRules.BOOLEAN),

  /** Group: Logic, Operation: Greater or equal */
  GREATEREQ(TypeRules.BOOLEAN),

  /** Group: Logic, Operation: Power */
  POWER(TypeRules.FIRST_NUM_ARG),

  /**
   * The items below belong to the "Logic Arithmetic (Additional)" group.
   */

  /** Group: Logic, Operation: Absolute value */
  ABS(TypeRules.FIRST_KNOWN_NUM_ARG),

  /** Group: Logic, Operation: Minimum */
  MIN(TypeRules.FIRST_KNOWN_NUM_ARG),

  /** Group: Logic, Operation: Maximum */
  MAX(TypeRules.FIRST_KNOWN_NUM_ARG),

  /**
   * The items below belong to the "Basic Bitvector Arithmetic" group.
   */

  /** Group: Bitvector, Operation: Addition */
  BVADD(TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Subtraction */
  BVSUB(TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Unary minus */
  BVNEG(TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Multiplication */
  BVMUL(TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Unsigned remainder */
  BVUREM(TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Signed remainder */
  BVSREM(TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Signed modulo */
  BVSMOD(TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Logical shift left */
  BVLSHL(TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Arithmetical shift left */
  BVASHL(TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Unsigned (BitVectorOperational) shift right */
  BVLSHR(TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Signed (arithmetical) shift right */
  BVASHR(TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Concatenation */
  BVCONCAT(TypeRules.UNKNOWN),

  /** Group: Bitvector, Operation: Replication (concatenation of several copies of bitvector) */
  BVREPEAT(TypeRules.UNKNOWN, 1),

  /** Group: Bitvector, Operation: Rotate left */
  BVROL(TypeRules.SECOND_VB_ARG, 1),

  /** Group: Bitvector, Operation: Rotate right */
  BVROR(TypeRules.SECOND_VB_ARG, 1),

  /** Group: Bitvector, Operation: Extension by zeros */
  BVZEROEXT(TypeRules.UNKNOWN, 1),

  /** Group: Bitvector, Operation: Extension to the signed equivalent */
  BVSIGNEXT(TypeRules.UNKNOWN, 1),

  /** Group: Bitvector, Operation: Extraction of subvector */
  BVEXTRACT(TypeRules.BVEXTRACT, 2),

  /**
   * The items below belong to the "Bitwise Operations" group.
   */

  /** Group: Bitvector, Operation: Bitwise OR */
  BVOR(TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Bitwise XOR */
  BVXOR(TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Bitwise AND */
  BVAND(TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Bitwise NOT */
  BVNOT(TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Bitwise NAND */
  BVNAND(TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Bitwise NOR */
  BVNOR(TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Bitwise XNOR */
  BVXNOR(TypeRules.FIRST_KNOWN_BV_ARG),

  /**
   * The items below belong to the "Predicates over Bitvectors" group.
   */

  /** Group: Bitvector, Operation: Unsigned less or equal */
  BVULE(TypeRules.BOOLEAN),

  /** Group: Bitvector, Operation: Unsigned less than */
  BVULT(TypeRules.BOOLEAN),

  /** Group: Bitvector, Operation: Unsigned greater or equal */
  BVUGE(TypeRules.BOOLEAN),

  /** Group: Bitvector, Operation: Unsigned greater than */
  BVUGT(TypeRules.BOOLEAN),

  /** Group: Bitvector, Operation: Signed less or equal */
  BVSLE(TypeRules.BOOLEAN),

  /** Group: Bitvector, Operation: Signed less than */
  BVSLT(TypeRules.BOOLEAN),

  /** Group: Bitvector, Operation: Signed greater or equal */
  BVSGE(TypeRules.BOOLEAN),

  /** Group: Bitvector, Operation: Signed greater than */
  BVSGT(TypeRules.BOOLEAN),

  /**
   * The items below belong to the "Bit Vector Reduction Operations" group.
   * 
   * Operation semantics:
   * 
   * <pre>
   * From IEEE Standard for Verilog Hardware Description Language:
   * 
   * The unary reduction operators shall perform a bitwise operation on a single operand
   * to produce a single-bit result. For reduction and, reduction or, and reduction xor operators,
   * the first step of the operation shall apply the operator between the first bit of the operand
   * and the second. The second and subsequent steps shall apply the operator between the 1-bit result
   * of the prior step and the next bit of the operand using the same logic table. For reduction nand,
   * reduction nor, and reduction xnor operators, the result shall be computed by inverting the result
   * of the reduction and, reduction or, and reduction xor operation, respectively.
   * 
   * See the manual for details.
   * </pre>
   */

  /** Group: Bit Vector Reduction, Operation: Reduction AND (&) */
  BVANDR(TypeRules.BIT_BOOLEAN),

  /** Group: Bit Vector Reduction, Operation: Reduction NAND (~&) */
  BVNANDR(TypeRules.BIT_BOOLEAN),

  /** Group: Bit Vector Reduction, Operation: Reduction OR (|) */
  BVORR(TypeRules.BIT_BOOLEAN),

  /** Group: Bit Vector Reduction, Operation: Reduction NOR (~|) */
  BVNORR(TypeRules.BIT_BOOLEAN),

  /** Group: Bit Vector Reduction, Operation: Reduction XOR (^) */
  BVXORR(TypeRules.BIT_BOOLEAN),

  /** Group: Bit Vector Reduction, Operation: Reduction XNOR (~^) */
  BVXNORR(TypeRules.BIT_BOOLEAN),

  /**
   * The items below belong to the "Array Operations" group.
   */

  /** Group: Array, Operation: Get stored value */
  SELECT(TypeRules.UNKNOWN),

  /** Group: Array, Operation: Store value */
  STORE(TypeRules.UNKNOWN);

  private final TypeRule typeRule;
  private final int numParams;

  private StandardOperation(TypeRule typeRule) {
    this(typeRule, 0);
  }

  private StandardOperation(TypeRule typeRule, int numParams) {
    this.typeRule = typeRule;
    this.numParams = numParams;
  }

  public static boolean isParametric(Enum<?> id) {
    return getParameterCount(id) != 0;
  }

  public static int getParameterCount(Enum<?> id) {
    if (!id.getClass().equals((StandardOperation.class))) {
      return 0;
    }

    return ((StandardOperation) id).numParams;
  }

  @Override
  public final DataType getResultType(DataType[] operandTypes, int[] params) {
    if (null == operandTypes) {
      throw new NullPointerException();
    }

    return typeRule.getResultType(operandTypes, params);
  }
}
