/*
 * Copyright 2012-2015 ISP RAS (http://www.ispras.ru)
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

import static ru.ispras.fortress.util.InvariantChecks.checkNotNull;

import java.util.Collection;
import java.util.EnumSet;
import java.util.LinkedList;
import java.util.Set;

import ru.ispras.fortress.data.DataType;

/**
 * The StandardOperation.java enumeration contains identifiers that specify particular operations
 * used in expressions.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public enum StandardOperation implements TypeRule {
  /**
   * The items below belong to the "Logic Operations" group.
   */

  /** Group: Logic, Operation: Equality */
  EQ(EnumSet.of(Family.LOGIC, Family.BV, Family.ARRAY), TypeRules.BOOLEAN, OperandTypes.SAME),

  /** Group: Logic, Operation: Not Equal */
  NOTEQ(EnumSet.of(Family.LOGIC, Family.BV, Family.ARRAY), TypeRules.BOOLEAN, OperandTypes.SAME),

  /** Group: Logic, Operation: Case equality */
  EQCASE(EnumSet.of(Family.LOGIC, Family.BV, Family.ARRAY), TypeRules.BOOLEAN, OperandTypes.SAME),

  /** Group: Logic, Operation: Case not equality */
  NOTEQCASE(EnumSet.of(Family.LOGIC, Family.BV, Family.ARRAY), TypeRules.BOOLEAN, OperandTypes.SAME),

  /** Group: Logic, Operation: AND */
  AND(Family.LOGIC, TypeRules.BOOLEAN, OperandTypes.BOOL),

  /** Group: Logic, Operation: OR */
  OR(Family.LOGIC, TypeRules.BOOLEAN, OperandTypes.BOOL),

  /** Group: Logic, Operation: NOT */
  NOT(Family.LOGIC, TypeRules.BOOLEAN, OperandTypes.BOOL),

  /** Group: Logic, Operation: XOR */
  XOR(Family.LOGIC, TypeRules.BOOLEAN, OperandTypes.BOOL),

  /** Group: Logic, Operation: Implication */
  IMPL(Family.LOGIC, TypeRules.BOOLEAN, OperandTypes.BOOL),

  /** Group: Logic, Operation: Conditional expression aka if-then-else */
  ITE(Family.LOGIC, TypeRules.ITE, OperandTypes.ITE),

  /**
   * The items below belong to the "Logic Arithmetic" group.
   */

  /** Group: Logic, Operation: Unary minus */
  MINUS(Family.LOGIC, TypeRules.FIRST_KNOWN_NUM_ARG, OperandTypes.LOGIC),

  /** Group: Logic, Operation: Unary plus */
  PLUS(Family.LOGIC, TypeRules.FIRST_KNOWN_NUM_ARG, OperandTypes.LOGIC),

  /** Group: Logic, Operation: Addition */
  ADD(Family.LOGIC, TypeRules.FIRST_KNOWN_NUM_ARG, OperandTypes.LOGIC_NUMERIC),

  /** Group: Logic, Operation: Subtraction */
  SUB(Family.LOGIC, TypeRules.FIRST_KNOWN_NUM_ARG, OperandTypes.LOGIC_NUMERIC),

  /** Group: Logic, Operation: Division */
  DIV(Family.LOGIC, TypeRules.FIRST_KNOWN_NUM_ARG, OperandTypes.LOGIC_NUMERIC),

  /** Group: Logic, Operation: Multiplication */
  MUL(Family.LOGIC, TypeRules.FIRST_KNOWN_NUM_ARG, OperandTypes.INT),

  /** Group: Logic, Operation: Remainder */
  REM(Family.LOGIC, TypeRules.FIRST_KNOWN_NUM_ARG, OperandTypes.INT),

  /** Group: Logic, Operation: Modulo */
  MOD(Family.LOGIC, TypeRules.FIRST_KNOWN_NUM_ARG, OperandTypes.INT),

  /** Group: Logic, Operation: Less */
  LESS(Family.LOGIC, TypeRules.BOOLEAN, OperandTypes.LOGIC_NUMERIC),

  /** Group: Logic, Operation: Less or equal */
  LESSEQ(Family.LOGIC, TypeRules.BOOLEAN, OperandTypes.LOGIC_NUMERIC),

  /** Group: Logic, Operation: Greater */
  GREATER(Family.LOGIC, TypeRules.BOOLEAN, OperandTypes.LOGIC_NUMERIC),

  /** Group: Logic, Operation: Greater or equal */
  GREATEREQ(Family.LOGIC, TypeRules.BOOLEAN, OperandTypes.LOGIC_NUMERIC),

  /** Group: Logic, Operation: Power */
  POWER(Family.LOGIC, TypeRules.FIRST_NUM_ARG, OperandTypes.INT),

  /**
   * The items below belong to the "Logic Arithmetic (Additional)" group.
   */

  /** Group: Logic, Operation: Absolute value */
  ABS(Family.LOGIC, TypeRules.FIRST_KNOWN_NUM_ARG, OperandTypes.LOGIC),

  /** Group: Logic, Operation: Minimum */
  MIN(Family.LOGIC, TypeRules.FIRST_KNOWN_NUM_ARG, OperandTypes.SAME),

  /** Group: Logic, Operation: Maximum */
  MAX(Family.LOGIC, TypeRules.FIRST_KNOWN_NUM_ARG, OperandTypes.SAME),

  /**
   * The items below belong to the "Basic Bitvector Arithmetic" group.
   */

  /** Group: Bitvector, Operation: Addition */
  BVADD(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG, OperandTypes.SAME_BV),

  /** Group: Bitvector, Operation: Subtraction */
  BVSUB(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG, OperandTypes.SAME_BV),

  /** Group: Bitvector, Operation: Unary minus */
  BVNEG(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG, OperandTypes.SAME_BV),

  /** Group: Bitvector, Operation: Multiplication */
  BVMUL(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG, OperandTypes.SAME_BV),

  /** Group: Bitvector, Operation: Unsigned division */
  BVUDIV(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG, OperandTypes.SAME_BV),

  /** Group: Bitvector, Operation: Signed division */
  BVSDIV(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG, OperandTypes.SAME_BV),

  /** Group: Bitvector, Operation: Unsigned remainder */
  BVUREM(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG, OperandTypes.SAME_BV),

  /** Group: Bitvector, Operation: Signed remainder */
  BVSREM(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG, OperandTypes.SAME_BV),

  /** Group: Bitvector, Operation: Signed modulo */
  BVSMOD(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG, OperandTypes.SAME_BV),

  /** Group: Bitvector, Operation: Logical shift left */
  BVLSHL(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG, OperandTypes.SAME_BV),

  /** Group: Bitvector, Operation: Arithmetical shift left */
  BVASHL(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG, OperandTypes.SAME_BV),

  /** Group: Bitvector, Operation: Unsigned (BitVectorOperational) shift right */
  BVLSHR(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG, OperandTypes.SAME_BV),

  /** Group: Bitvector, Operation: Signed (arithmetical) shift right */
  BVASHR(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG, OperandTypes.SAME_BV),

  /** Group: Bitvector, Operation: Concatenation */
  BVCONCAT(Family.BV, TypeRules.BVCONCAT, OperandTypes.BV),

  /** Group: Bitvector, Operation: Replication (concatenation of several copies of bitvector) */
  BVREPEAT(Family.BV, TypeRules.BVREPEAT, 1, OperandTypes.ONE_INT_PARAM_BV),

  /** Group: Bitvector, Operation: Rotate left */
  BVROL(Family.BV, TypeRules.SECOND_VB_ARG, 1, OperandTypes.ONE_INT_PARAM_BV),

  /** Group: Bitvector, Operation: Rotate right */
  BVROR(Family.BV, TypeRules.SECOND_VB_ARG, 1, OperandTypes.ONE_INT_PARAM_BV),

  /** Group: Bitvector, Operation: Extension by zeros */
  BVZEROEXT(Family.BV, TypeRules.BVEXTEND, 1, OperandTypes.ONE_INT_PARAM_BV),

  /** Group: Bitvector, Operation: Extension to the signed equivalent */
  BVSIGNEXT(Family.BV, TypeRules.BVEXTEND, 1, OperandTypes.ONE_INT_PARAM_BV),

  /** Group: Bitvector, Operation: Extraction of subvector */
  BVEXTRACT(Family.BV, TypeRules.BVEXTRACT, 2, OperandTypes.TWO_INT_PARAM_BV),

  /**
   * The items below belong to the "Bitwise Operations" group.
   */

  /** Group: Bitvector, Operation: Bitwise OR */
  BVOR(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG, OperandTypes.SAME_BV),

  /** Group: Bitvector, Operation: Bitwise XOR */
  BVXOR(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG, OperandTypes.SAME_BV),

  /** Group: Bitvector, Operation: Bitwise AND */
  BVAND(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG, OperandTypes.SAME_BV),

  /** Group: Bitvector, Operation: Bitwise NOT */
  BVNOT(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG, OperandTypes.SAME_BV),

  /** Group: Bitvector, Operation: Bitwise NAND */
  BVNAND(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG, OperandTypes.SAME_BV),

  /** Group: Bitvector, Operation: Bitwise NOR */
  BVNOR(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG, OperandTypes.SAME_BV),

  /** Group: Bitvector, Operation: Bitwise XNOR */
  BVXNOR(Family.BV, TypeRules.FIRST_KNOWN_BV_ARG, OperandTypes.SAME_BV),

  /**
   * The items below belong to the "Predicates over Bitvectors" group.
   */

  /** Group: Bitvector, Operation: Unsigned less or equal */
  BVULE(Family.BV, TypeRules.BOOLEAN, OperandTypes.SAME_BV),

  /** Group: Bitvector, Operation: Unsigned less than */
  BVULT(Family.BV, TypeRules.BOOLEAN, OperandTypes.SAME_BV),

  /** Group: Bitvector, Operation: Unsigned greater or equal */
  BVUGE(Family.BV, TypeRules.BOOLEAN, OperandTypes.SAME_BV),

  /** Group: Bitvector, Operation: Unsigned greater than */
  BVUGT(Family.BV, TypeRules.BOOLEAN, OperandTypes.SAME_BV),

  /** Group: Bitvector, Operation: Signed less or equal */
  BVSLE(Family.BV, TypeRules.BOOLEAN, OperandTypes.SAME_BV),

  /** Group: Bitvector, Operation: Signed less than */
  BVSLT(Family.BV, TypeRules.BOOLEAN, OperandTypes.SAME_BV),

  /** Group: Bitvector, Operation: Signed greater or equal */
  BVSGE(Family.BV, TypeRules.BOOLEAN, OperandTypes.SAME_BV),

  /** Group: Bitvector, Operation: Signed greater than */
  BVSGT(Family.BV, TypeRules.BOOLEAN, OperandTypes.SAME_BV),

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
  BVANDR(Family.BV, TypeRules.BIT_BOOLEAN, OperandTypes.SAME_BV),

  /** Group: Bit Vector Reduction, Operation: Reduction NAND (~&) */
  BVNANDR(Family.BV, TypeRules.BIT_BOOLEAN, OperandTypes.SAME_BV),

  /** Group: Bit Vector Reduction, Operation: Reduction OR (|) */
  BVORR(Family.BV, TypeRules.BIT_BOOLEAN, OperandTypes.SAME_BV),

  /** Group: Bit Vector Reduction, Operation: Reduction NOR (~|) */
  BVNORR(Family.BV, TypeRules.BIT_BOOLEAN, OperandTypes.SAME_BV),

  /** Group: Bit Vector Reduction, Operation: Reduction XOR (^) */
  BVXORR(Family.BV, TypeRules.BIT_BOOLEAN, OperandTypes.SAME_BV),

  /** Group: Bit Vector Reduction, Operation: Reduction XNOR (~^) */
  BVXNORR(Family.BV, TypeRules.BIT_BOOLEAN, OperandTypes.SAME_BV),

  /**
   * The items below belong to the "Bit Vector Cast Operations" group.
   */

  /** Group: Bit Vector Cast, Operation: Cast to boolean */
  BV2BOOL(Family.BV, TypeRules.BOOLEAN, OperandTypes.SAME_BV),

  /** Group: Bit Vector Cast, Operation: Cast boolean to bit vector of size 1 */
  BOOL2BV(Family.BV, TypeRules.BIT_BOOLEAN, OperandTypes.BOOL),

  /**
   * The items below belong to the "Array Operations" group.
   */

  /** Group: Array, Operation: Get stored value */
  SELECT(Family.ARRAY, TypeRules.SELECT, OperandTypes.SELECT),

  /** Group: Array, Operation: Store value */
  STORE(Family.ARRAY, TypeRules.STORE, OperandTypes.STORE);

  /**
   * Describes the family of operands the operation manipulates with.
   */
  public enum Family {
    LOGIC, BV, ARRAY
  }

  private final Set<Family> family;
  private final TypeRule typeRule;
  private final OperandTypes operandTypes;
  private final int numParams;

  StandardOperation(
      final Family family,
      final TypeRule typeRule,
      final OperandTypes operandTypes) {

    this(EnumSet.of(family), typeRule, operandTypes);
  }

  StandardOperation(
      final Set<Family> family,
      final TypeRule typeRule,
      final OperandTypes operandTypes) {

    this(family, typeRule, 0, operandTypes);
  }

  StandardOperation(
      final Family family,
      final TypeRule typeRule,
      final int numParams,
      final OperandTypes operandTypes) {

    this(EnumSet.of(family), typeRule, numParams, operandTypes);
  }

  StandardOperation(
      final Set<Family> family,
      final TypeRule typeRule,
      final int numParams,
      final OperandTypes operandTypes) {

    this.family = family;
    this.typeRule = typeRule;
    this.operandTypes = operandTypes;
    this.numParams = numParams;
  }

  public static boolean isParametric(final Enum<?> id) {
    return getParameterCount(id) != 0;
  }

  public static int getParameterCount(final Enum<?> id) {
    if (!(id instanceof StandardOperation)) {
      return 0;
    }

    return ((StandardOperation) id).numParams;
  }

  public static boolean isFamily(final Enum<?> id, final Family family) {
    return id instanceof StandardOperation && ((StandardOperation) id).family.contains(family);
  }

  /**
   * Returns the collection of operations are defined on same type operands.
   *
   * @return The collection of operations are defined on same type operands.
   */
  public static Collection<Enum<?>> getSameOperandOperations() {
    return getOperations(OperandTypes.SAME);
  }

  /**
   * Returns the collection of operations are defined on same bit vector type operands.
   *
   * @return The collection of operations are defined on same bit vector type operands.
   */
  public static Collection<Enum<?>> getSameBvOperandOperations() {
    return getOperations(OperandTypes.SAME_BV);
  }

  /**
   * Returns the collection of operations are defined on operands of logic types.
   *
   * @return The collection of operations are defined on operands of logic types.
   */
  public static Collection<Enum<?>> getLogicOperandOperations() {
    return getOperations(OperandTypes.LOGIC);
  }

  /**
   * Returns the collection of operations are defined on operands of logic numeric type.
   *
   * @return The collection of operations are defined on operands of logic numeric type.
   */
  public static Collection<Enum<?>> getSameLogicNumOperandOperations() {
    return getOperations(OperandTypes.LOGIC_NUMERIC);
  }

  /**
   * Returns the collection of operations are defined on operands of integer type.
   *
   * @return The collection of operations are defined on operands of integer type.
   */
  public static Collection<Enum<?>> getIntOperandOperations() {
    return getOperations(OperandTypes.INT);
  }

  /**
   * Returns the collection of operations are defined on operands of boolean type.
   *
   * @return The collection of operations are defined on operands of boolean type.
   */
  public static Collection<Enum<?>> getBoolOperandOperations() {
    return getOperations(OperandTypes.BOOL);
  }

  /**
   * Returns the collection of operations are defined on operands of different bit vector types.
   *
   * @return The collection of operations are defined on operands of different bit vector types.
   */
  public static Collection<Enum<?>> getDifferentBvOperandOperations() {
    return getOperations(OperandTypes.BV);
  }

  /**
   * Returns the collection of operations are defined on operands of following types -
   * one integer parameter and one bit vector operand.
   *
   * @return The collection of operations are defined on operands of following types -
   *         one integer parameter and one bit vector operand.
   */
  public static Collection<Enum<?>> getOneIntParamBvOperandOperations() {
    return getOperations(OperandTypes.ONE_INT_PARAM_BV);
  }

  /**
   * Returns the collection of operations are defined on operands of following types -
   * two integer parameters and one bit vector operand.
   *
   * @return The collection of operations are defined on operands of following types -
   *         two integer parameters and one bit vector operand.
   */
  public static Collection<Enum<?>> getTwoIntParamBvOperandOperations() {
    return getOperations(OperandTypes.TWO_INT_PARAM_BV);
  }

  /**
   * Returns the collection of operations are defined on operands of bit vector type.
   *
   * @return The collection of operations are defined on operands of bit vector type.
   */
  public static Collection<Enum<?>> getBvOperandOperations() {
    final Collection<Enum<?>> operations = new LinkedList<>();

    operations.addAll(getSameBvOperandOperations());
    operations.addAll(getDifferentBvOperandOperations());
    operations.addAll(getOneIntParamBvOperandOperations());
    operations.addAll(getTwoIntParamBvOperandOperations());

    return operations;
  }

  /**
   * Returns the collection of parametric operation identifiers.
   * @return The collection of parametric operation identifiers.
   */
  public static Collection<Enum<?>> getParamOperations() {
    final Collection<Enum<?>> operations = new LinkedList<>();

    for (int i = 0; i < StandardOperation.values().length; i++) {

      final StandardOperation operation = StandardOperation.values()[i];
      if (StandardOperation.getParameterCount(operation) > 0) {
        operations.add(operation);
      }
    }

    return operations;
  }

  private static Collection<Enum<?>> getOperations(final Enum<?> operandTypesId) {
    final Collection<Enum<?>> operations = new LinkedList<>();

    for (int i = 0; i < StandardOperation.values().length; i++) {

      final StandardOperation operation = StandardOperation.values()[i];
      if (operation.operandTypes == operandTypesId) {
        operations.add(operation);
      }
    }

    return operations;
  }

  @Override
  public final DataType getResultType(final DataType[] operandTypes, final int[] params) {
    checkNotNull(operandTypes);
    return typeRule.getResultType(operandTypes, params);
  }
}
