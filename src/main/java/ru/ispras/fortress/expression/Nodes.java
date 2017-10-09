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

  public static NodeOperation MINUS(final Node operand) {
    return new NodeOperation(StandardOperation.MINUS, operand);
  }

  public static NodeOperation PLUS(final Node operand) {
    return new NodeOperation(StandardOperation.PLUS, operand);
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
  IMPL
  ITE
  MINUS +
  PLUS +
  ADD
  SUB
  DIV
  MUL
  REM
  MOD
  LESS
  LESSEQ
  GREATER
  GREATEREQ
  POWER
  ABS
  MIN
  MAX
  BVADD
  BVSUB
  BVNEG
  BVMUL
  BVUDIV
  BVSDIV
  BVUREM
  BVSREM
  BVSMOD
  BVLSHL
  BVASHL
  BVLSHR
  BVASHR
  BVCONCAT
  BVREPEAT
  BVROL
  BVROR
  BVZEROEXT
  BVSIGNEXT
  BVEXTRACT
  BVOR
  BVXOR
  BVAND
  BVNOT
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
