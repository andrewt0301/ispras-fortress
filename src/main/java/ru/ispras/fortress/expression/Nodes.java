/*
 * Copyright 2017 ISP RAS (http://www.ispras.ru)
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

import java.util.List;

/**
 * The {@link Node} class provides utility methods to work with node objects.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public final class Nodes {
  private Nodes() {}

  public static final Node TRUE = NodeValue.newBoolean(true);
  public static final Node FALSE = NodeValue.newBoolean(false);

  public static NodeOperation EQ(final Node lhs, final Node rhs) {
    return new NodeOperation(StandardOperation.EQ, lhs, rhs);
  }

  public static NodeOperation NOTEQ(final Node lhs, final Node rhs) {
    return new NodeOperation(StandardOperation.NOTEQ, lhs, rhs);
  }

  public static NodeOperation EQCASE(final Node lhs, final Node rhs) {
    return new NodeOperation(StandardOperation.EQCASE, lhs, rhs);
  }

  public static NodeOperation NOTEQCASE(final Node lhs, final Node rhs) {
    return new NodeOperation(StandardOperation.NOTEQCASE, lhs, rhs);
  }

  public static NodeOperation AND(final Node... operands) {
    return new NodeOperation(StandardOperation.AND, operands);
  }

  public static NodeOperation AND(final List<? extends Node> operands) {
    return new NodeOperation(StandardOperation.AND, operands);
  }

  public static NodeOperation OR(final Node... operands) {
    return new NodeOperation(StandardOperation.OR, operands);
  }

  public static NodeOperation OR(final List<? extends Node> operands) {
    return new NodeOperation(StandardOperation.OR, operands);
  }

  public static NodeOperation NOT(final Node operand) {
    return new NodeOperation(StandardOperation.NOT, operand);
  }

  public static NodeOperation XOR(final Node... operands) {
    return new NodeOperation(StandardOperation.XOR, operands);
  }

  public static NodeOperation XOR(final List<? extends Node> operands) {
    return new NodeOperation(StandardOperation.XOR, operands);
  }

  public static NodeOperation IMPL(final Node first, final Node second) {
    return new NodeOperation(StandardOperation.IMPL, first, second);
  }

  public static NodeOperation MINUS(final Node operand) {
    return new NodeOperation(StandardOperation.MINUS, operand);
  }

  public static NodeOperation PLUS(final Node operand) {
    return new NodeOperation(StandardOperation.PLUS, operand);
  }

  public static NodeOperation ADD(final Node... operands) {
    return new NodeOperation(StandardOperation.ADD, operands);
  }

  public static NodeOperation ADD(final List<? extends Node> operands) {
    return new NodeOperation(StandardOperation.ADD, operands);
  }

  public static NodeOperation SUB(final Node... operands) {
    return new NodeOperation(StandardOperation.SUB, operands);
  }

  public static NodeOperation SUB(final List<? extends Node> operands) {
    return new NodeOperation(StandardOperation.SUB, operands);
  }

  public static NodeOperation DIV(final Node first, final Node second) {
    return new NodeOperation(StandardOperation.DIV, first, second);
  }

  public static NodeOperation MUL(final Node... operands) {
    return new NodeOperation(StandardOperation.MUL, operands);
  }

  public static NodeOperation MUL(final List<? extends Node> operands) {
    return new NodeOperation(StandardOperation.MUL, operands);
  }

  public static NodeOperation REM(final Node first, final Node second) {
    return new NodeOperation(StandardOperation.REM, first, second);
  }

  public static NodeOperation MOD(final Node first, final Node second) {
    return new NodeOperation(StandardOperation.MOD, first, second);
  }

  public static NodeOperation LESS(final Node lhs, final Node rhs) {
    return new NodeOperation(StandardOperation.LESS, lhs, rhs);
  }

  public static NodeOperation LESSEQ(final Node lhs, final Node rhs) {
    return new NodeOperation(StandardOperation.LESSEQ, lhs, rhs);
  }

  public static NodeOperation GREATER(final Node lhs, final Node rhs) {
    return new NodeOperation(StandardOperation.GREATER, lhs, rhs);
  }

  public static NodeOperation GREATEREQ(final Node lhs, final Node rhs) {
    return new NodeOperation(StandardOperation.GREATEREQ, lhs, rhs);
  }

  public static NodeOperation POWER(final Node base, final Node exponent) {
    return new NodeOperation(StandardOperation.POWER, base, exponent);
  }

  public static NodeOperation ABS(final Node operand) {
    return new NodeOperation(StandardOperation.ABS, operand);
  }

  public static NodeOperation MIN(final Node... operands) {
    return new NodeOperation(StandardOperation.MIN, operands);
  }

  public static NodeOperation MIN(final List<? extends Node> operands) {
    return new NodeOperation(StandardOperation.MIN, operands);
  }

  public static NodeOperation MAX(final Node... operands) {
    return new NodeOperation(StandardOperation.MAX, operands);
  }

  public static NodeOperation MAX(final List<? extends Node> operands) {
    return new NodeOperation(StandardOperation.MAX, operands);
  }

  public static NodeOperation BVADD(final Node... operands) {
    return new NodeOperation(StandardOperation.BVADD, operands);
  }

  public static NodeOperation BVADD(final List<? extends Node> operands) {
    return new NodeOperation(StandardOperation.BVADD, operands);
  }

  public static NodeOperation BVSUB(final Node... operands) {
    return new NodeOperation(StandardOperation.BVSUB, operands);
  }

  public static NodeOperation BVSUB(final List<? extends Node> operands) {
    return new NodeOperation(StandardOperation.BVSUB, operands);
  }

  public static NodeOperation BVNEG(final Node operand) {
    return new NodeOperation(StandardOperation.BVNEG, operand);
  }

  public static NodeOperation BVMUL(final Node... operands) {
    return new NodeOperation(StandardOperation.BVMUL, operands);
  }

  public static NodeOperation BVMUL(final List<? extends Node> operands) {
    return new NodeOperation(StandardOperation.BVMUL, operands);
  }

  public static NodeOperation BVUDIV(final Node first, final Node second) {
    return new NodeOperation(StandardOperation.BVUDIV, first, second);
  }

  public static NodeOperation BVSDIV(final Node first, final Node second) {
    return new NodeOperation(StandardOperation.BVSDIV, first, second);
  }

  public static NodeOperation BVUREM(final Node first, final Node second) {
    return new NodeOperation(StandardOperation.BVUREM, first, second);
  }

  public static NodeOperation BVSREM(final Node first, final Node second) {
    return new NodeOperation(StandardOperation.BVSREM, first, second);
  }

  public static NodeOperation BVSMOD(final Node first, final Node second) {
    return new NodeOperation(StandardOperation.BVSMOD, first, second);
  }

  public static NodeOperation BVLSHL(final Node source, final Node amount) {
    return new NodeOperation(StandardOperation.BVLSHL, source, amount);
  }

  public static NodeOperation BVASHL(final Node source, final Node amount) {
    return new NodeOperation(StandardOperation.BVASHL, source, amount);
  }

  public static NodeOperation BVLSHR(final Node source, final Node amount) {
    return new NodeOperation(StandardOperation.BVLSHR, source, amount);
  }

  public static NodeOperation BVASHR(final Node source, final Node amount) {
    return new NodeOperation(StandardOperation.BVASHR, source, amount);
  }

  public static NodeOperation BVCONCAT(final Node... operands) {
    return new NodeOperation(StandardOperation.BVCONCAT, operands);
  }

  public static NodeOperation BVCONCAT(final List<? extends Node> operands) {
    return new NodeOperation(StandardOperation.BVCONCAT, operands);
  }

  public static NodeOperation BVULE(final Node lhs, final Node rhs) {
    return new NodeOperation(StandardOperation.BVULE, lhs, rhs);
  }

  public static NodeOperation BVULT(final Node lhs, final Node rhs) {
    return new NodeOperation(StandardOperation.BVULT, lhs, rhs);
  }

  public static NodeOperation BVUGE(final Node lhs, final Node rhs) {
    return new NodeOperation(StandardOperation.BVUGE, lhs, rhs);
  }

  public static NodeOperation BVUGT(final Node lhs, final Node rhs) {
    return new NodeOperation(StandardOperation.BVUGT, lhs, rhs);
  }

  public static NodeOperation BVSLE(final Node lhs, final Node rhs) {
    return new NodeOperation(StandardOperation.BVSLE, lhs, rhs);
  }

  public static NodeOperation BVSLT(final Node lhs, final Node rhs) {
    return new NodeOperation(StandardOperation.BVSLT, lhs, rhs);
  }

  public static NodeOperation BVSGE(final Node lhs, final Node rhs) {
    return new NodeOperation(StandardOperation.BVSGE, lhs, rhs);
  }

  public static NodeOperation BVSGT(final Node lhs, final Node rhs) {
    return new NodeOperation(StandardOperation.BVSGT, lhs, rhs);
  }

  public static NodeOperation BVEXTRACT(
      final Node source,
      final NodeValue low,
      final NodeValue high) {
    return new NodeOperation(StandardOperation.BVEXTRACT, high, low, source);
  }

  public static NodeOperation BVEXTRACT(final Node source, final NodeValue bit) {
    return BVEXTRACT(source, bit, bit);
  }

  public static NodeOperation BVEXTRACT(final Node source, final int low, final int high) {
    return BVEXTRACT(source, NodeValue.newInteger(low), NodeValue.newInteger(high));
  }

  public static NodeOperation BVEXTRACT(final Node source, final int bit) {
    return BVEXTRACT(source, NodeValue.newInteger(bit));
  }

  public static NodeOperation BVEXTRACT(final Node source, final NodeValue low, final int high) {
    return BVEXTRACT(source, low, NodeValue.newInteger(high));
  }

  public static NodeOperation BVEXTRACT(final Node source, final int low, final NodeValue high) {
    return BVEXTRACT(source, NodeValue.newInteger(low), high);
  }

  public static NodeOperation BVOR(final Node... operands) {
    return new NodeOperation(StandardOperation.BVOR, operands);
  }

  public static NodeOperation BVOR(final List<? extends Node> operands) {
    return new NodeOperation(StandardOperation.BVOR, operands);
  }

  public static NodeOperation BVXOR(final Node... operands) {
    return new NodeOperation(StandardOperation.BVXOR, operands);
  }

  public static NodeOperation BVXOR(final List<? extends Node> operands) {
    return new NodeOperation(StandardOperation.BVXOR, operands);
  }

  public static NodeOperation BVAND(final Node... operands) {
    return new NodeOperation(StandardOperation.BVAND, operands);
  }

  public static NodeOperation BVAND(final List<? extends Node> operands) {
    return new NodeOperation(StandardOperation.BVAND, operands);
  }

  public static NodeOperation BVNOT(final Node operand) {
    return new NodeOperation(StandardOperation.BVNOT, operand);
  }

  public static NodeOperation STORE(final Node array, final Node key, final Node value) {
    return new NodeOperation(StandardOperation.STORE, array, key, value);
  }

  public static NodeOperation SELECT(final Node array, final Node key) {
    return new NodeOperation(StandardOperation.SELECT, array, key);
  }

  /* TODO:

  EQ +
  NOTEQ +
  EQCASE +
  NOTEQCASE +
  AND +
  OR +
  NOT +
  XOR +
  IMPL +
  ITE
  MINUS +
  PLUS +
  ADD +
  SUB +
  DIV +
  MUL +
  REM +
  MOD +
  LESS +
  LESSEQ +
  GREATER +
  GREATEREQ +
  POWER +
  ABS +
  MIN +
  MAX +
  BVADD +
  BVSUB +
  BVNEG +
  BVMUL +
  BVUDIV +
  BVSDIV +
  BVUREM +
  BVSREM +
  BVSMOD +
  BVLSHL +
  BVASHL +
  BVLSHR +
  BVASHR +
  BVCONCAT +
  BVREPEAT
  BVROL
  BVROR
  BVZEROEXT
  BVSIGNEXT
  BVEXTRACT +
  BVOR +
  BVXOR +
  BVAND +
  BVNOT +
  BVNAND
  BVNOR
  BVXNOR
  BVULE +
  BVULT +
  BVUGE +
  BVUGT +
  BVSLE +
  BVSLT +
  BVSGE +
  BVSGT +
  BVANDR
  BVNANDR
  BVORR
  BVNORR
  BVXORR
  BVXNORR
  BV2BOOL
  BOOL2BV
  BV2INT
  INT2BV
  SELECT +
  STORE +
  */
}
