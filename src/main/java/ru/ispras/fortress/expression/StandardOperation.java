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

import java.util.EnumSet;
import java.util.Set;

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
  EQ(EnumSet.of(Family.LOGIC, Family.BV, Family.ARRAY), TypeRules.BOOLEAN),

  /** Group: Logic, Operation: Not Equal */
  NOTEQ(EnumSet.of(Family.LOGIC, Family.BV, Family.ARRAY), TypeRules.BOOLEAN),

  /** Group: Logic, Operation: Case equality */
  EQCASE(EnumSet.of(Family.LOGIC, Family.BV, Family.ARRAY), TypeRules.BOOLEAN),

  /** Group: Logic, Operation: Case not equality */
  NOTEQCASE(EnumSet.of(Family.LOGIC, Family.BV, Family.ARRAY), TypeRules.BOOLEAN),

  /** Group: Logic, Operation: AND */
  AND(Family.LOGIC, TypeRules.BOOLEAN),

  /** Group: Logic, Operation: OR */
  OR(Family.LOGIC, TypeRules.BOOLEAN),

  /** Group: Logic, Operation: NOT */
  NOT(Family.LOGIC, TypeRules.BOOLEAN),

  /** Group: Logic, Operation: XOR */
  XOR(Family.LOGIC, TypeRules.BOOLEAN),

  /** Group: Logic, Operation: Implication */
  IMPL(Family.LOGIC, TypeRules.BOOLEAN),

  /** Group: Logic, Operation: Conditional expression aka if-then-else */
  ITE(Family.LOGIC, TypeRules.ITE),

  /**
   * The items below belong to the "Logic Arithmetic" group.
   */

  /** Group: Logic, Operation: Unary minus */
  MINUS(Family.LOGIC, TypeRules.FIRST_KNOWN_NUM_ARG),

  /** Group: Logic, Operation: Unary plus */
  PLUS(Family.LOGIC, TypeRules.FIRST_KNOWN_NUM_ARG),

  /** Group: Logic, Operation: Addition */
  ADD(Family.LOGIC, TypeRules.FIRST_KNOWN_NUM_ARG),

  /** Group: Logic, Operation: Subtraction */
  SUB(Family.LOGIC, TypeRules.FIRST_KNOWN_NUM_ARG),

  /** Group: Logic, Operation: Division */
  DIV(Family.LOGIC, TypeRules.FIRST_KNOWN_NUM_ARG),

  /** Group: Logic, Operation: Multiplication */
  MUL(Family.LOGIC, TypeRules.FIRST_KNOWN_NUM_ARG),

  /** Group: Logic, Operation: Remainder */
  REM(Family.LOGIC, TypeRules.FIRST_KNOWN_NUM_ARG),

  /** Group: Logic, Operation: Modulo */
  MOD(Family.LOGIC, TypeRules.FIRST_KNOWN_NUM_ARG),

  /** Group: Logic, Operation: Less */
  LESS(Family.LOGIC, TypeRules.BOOLEAN),

  /** Group: Logic, Operation: Less or equal */
  LESSEQ(Family.LOGIC, TypeRules.BOOLEAN),

  /** Group: Logic, Operation: Greater */
  GREATER(Family.LOGIC, TypeRules.BOOLEAN),

  /** Group: Logic, Operation: Greater or equal */
  GREATEREQ(Family.LOGIC, TypeRules.BOOLEAN),

  /** Group: Logic, Operation: Power */
  POWER(Family.LOGIC, TypeRules.FIRST_NUM_ARG),

  /**
   * The items below belong to the "Logic Arithmetic (Additional)" group.
   */

  /** Group: Logic, Operation: Absolute value */
  ABS(Family.LOGIC, TypeRules.FIRST_KNOWN_NUM_ARG),

  /** Group: Logic, Operation: Minimum */
  MIN(Family.LOGIC, TypeRules.FIRST_KNOWN_NUM_ARG),

  /** Group: Logic, Operation: Maximum */
  MAX(Family.LOGIC, TypeRules.FIRST_KNOWN_NUM_ARG),

  /**
   * The items below belong to the "Basic Bitvector Arithmetic" group.
   */

  /** Group: Bitvector, Operation: Addition */
  BVADD(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Subtraction */
  BVSUB(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Unary minus */
  BVNEG(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Multiplication */
  BVMUL(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Unsigned remainder */
  BVUREM(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Signed remainder */
  BVSREM(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Signed modulo */
  BVSMOD(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Logical shift left */
  BVLSHL(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Arithmetical shift left */
  BVASHL(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Unsigned (BitVectorOperational) shift right */
  BVLSHR(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Signed (arithmetical) shift right */
  BVASHR(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Concatenation */
  BVCONCAT(Family.BV, TypeRules.UNKNOWN),

  /** Group: Bitvector, Operation: Replication (concatenation of several copies of bitvector) */
  BVREPEAT(Family.BV, TypeRules.UNKNOWN, 1),

  /** Group: Bitvector, Operation: Rotate left */
  BVROL(Family.BV, TypeRules.SECOND_VB_ARG, 1),

  /** Group: Bitvector, Operation: Rotate right */
  BVROR(Family.BV, TypeRules.SECOND_VB_ARG, 1),

  /** Group: Bitvector, Operation: Extension by zeros */
  BVZEROEXT(Family.BV, TypeRules.UNKNOWN, 1),

  /** Group: Bitvector, Operation: Extension to the signed equivalent */
  BVSIGNEXT(Family.BV, TypeRules.UNKNOWN, 1),

  /** Group: Bitvector, Operation: Extraction of subvector */
  BVEXTRACT(Family.BV, TypeRules.BVEXTRACT, 2),

  /**
   * The items below belong to the "Bitwise Operations" group.
   */

  /** Group: Bitvector, Operation: Bitwise OR */
  BVOR(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Bitwise XOR */
  BVXOR(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Bitwise AND */
  BVAND(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Bitwise NOT */
  BVNOT(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Bitwise NAND */
  BVNAND(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Bitwise NOR */
  BVNOR(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG),

  /** Group: Bitvector, Operation: Bitwise XNOR */
  BVXNOR(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG),

  /**
   * The items below belong to the "Predicates over Bitvectors" group.
   */

  /** Group: Bitvector, Operation: Unsigned less or equal */
  BVULE(Family.BV, TypeRules.BOOLEAN),

  /** Group: Bitvector, Operation: Unsigned less than */
  BVULT(Family.BV, TypeRules.BOOLEAN),

  /** Group: Bitvector, Operation: Unsigned greater or equal */
  BVUGE(Family.BV, TypeRules.BOOLEAN),

  /** Group: Bitvector, Operation: Unsigned greater than */
  BVUGT(Family.BV, TypeRules.BOOLEAN),

  /** Group: Bitvector, Operation: Signed less or equal */
  BVSLE(Family.BV, TypeRules.BOOLEAN),

  /** Group: Bitvector, Operation: Signed less than */
  BVSLT(Family.BV, TypeRules.BOOLEAN),

  /** Group: Bitvector, Operation: Signed greater or equal */
  BVSGE(Family.BV, TypeRules.BOOLEAN),

  /** Group: Bitvector, Operation: Signed greater than */
  BVSGT(Family.BV, TypeRules.BOOLEAN),

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
  BVANDR(Family.BV, TypeRules.BIT_BOOLEAN),

  /** Group: Bit Vector Reduction, Operation: Reduction NAND (~&) */
  BVNANDR(Family.BV, TypeRules.BIT_BOOLEAN),

  /** Group: Bit Vector Reduction, Operation: Reduction OR (|) */
  BVORR(Family.BV, TypeRules.BIT_BOOLEAN),

  /** Group: Bit Vector Reduction, Operation: Reduction NOR (~|) */
  BVNORR(Family.BV, TypeRules.BIT_BOOLEAN),

  /** Group: Bit Vector Reduction, Operation: Reduction XOR (^) */
  BVXORR(Family.BV, TypeRules.BIT_BOOLEAN),

  /** Group: Bit Vector Reduction, Operation: Reduction XNOR (~^) */
  BVXNORR(Family.BV, TypeRules.BIT_BOOLEAN),

  /**
   * The items below belong to the "Array Operations" group.
   */

  /** Group: Array, Operation: Get stored value */
  SELECT(Family.ARRAY, TypeRules.UNKNOWN),

  /** Group: Array, Operation: Store value */
  STORE(Family.ARRAY, TypeRules.UNKNOWN);

  /**
   * Describes the family of operands the operation manipulates with. 
   */

  public static enum Family {
    LOGIC, BV, ARRAY;
  }

  private final Set<Family> family;
  private final TypeRule typeRule;
  private final int numParams;

  private StandardOperation(Family family, TypeRule typeRule) {
    this(EnumSet.of(family), typeRule);
  }

  private StandardOperation(Set<Family> family, TypeRule typeRule) {
    this(family, typeRule, 0);
  }

  private StandardOperation(Family family, TypeRule typeRule, int numParams) {
    this(EnumSet.of(family), typeRule, numParams);
  }

  private StandardOperation(Set<Family> family, TypeRule typeRule, int numParams) {
    this.family = family;
    this.typeRule = typeRule;
    this.numParams = numParams;
  }

  public static boolean isParametric(Enum<?> id) {
    return getParameterCount(id) != 0;
  }

  public static int getParameterCount(Enum<?> id) {
    if (!(id instanceof StandardOperation)) {
      return 0;
    }

    return ((StandardOperation) id).numParams;
  }

  public static boolean isFamily(Enum<?> id, Family family) {
    if (!(id instanceof StandardOperation)) {
      return false;
    }

    return ((StandardOperation) id).family.contains(family);
  }

  @Override
  public final DataType getResultType(DataType[] operandTypes, int[] params) {
    if (null == operandTypes) {
      throw new NullPointerException();
    }

    return typeRule.getResultType(operandTypes, params);
  }
}
