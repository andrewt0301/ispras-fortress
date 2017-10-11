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

import ru.ispras.fortress.data.Variable;

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

  public static NodeOperation ITE(final Node condition, final Node first, final Node second) {
    return new NodeOperation(StandardOperation.ITE, condition, first, second);
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

  public static NodeOperation BVROL(final NodeValue amount, final Node source) {
    return new NodeOperation(StandardOperation.BVROL, amount, source);
  }

  public static NodeOperation BVROL(final int amount, final Node source) {
    return BVROL(NodeValue.newInteger(amount), source);
  }

  public static NodeOperation BVROR(final NodeValue amount, final Node source) {
    return new NodeOperation(StandardOperation.BVROR, amount, source);
  }

  public static NodeOperation BVROR(final int amount, final Node source) {
    return BVROR(NodeValue.newInteger(amount), source);
  }

  public static NodeOperation BVZEROEXT(final NodeValue deltaSize, final Node source) {
    return new NodeOperation(StandardOperation.BVZEROEXT, deltaSize, source);
  }

  public static NodeOperation BVZEROEXT(final int deltaSize, final Node source) {
    return BVZEROEXT(NodeValue.newInteger(deltaSize), source);
  }

  public static NodeOperation BVSIGNEXT(final NodeValue deltaSize, final Node source) {
    return new NodeOperation(StandardOperation.BVSIGNEXT, deltaSize, source);
  }

  public static NodeOperation BVSIGNEXT(final int deltaSize, final Node source) {
    return BVSIGNEXT(NodeValue.newInteger(deltaSize), source);
  }

  public static NodeOperation BVEXTRACT(
      final NodeValue high,
      final NodeValue low,
      final Node source) {
    return new NodeOperation(StandardOperation.BVEXTRACT, high, low, source);
  }

  public static NodeOperation BVEXTRACT(final NodeValue bit, final Node source) {
    return BVEXTRACT(bit, bit, source);
  }

  public static NodeOperation BVEXTRACT(final int high, final int low, final Node source) {
    return BVEXTRACT(NodeValue.newInteger(high), NodeValue.newInteger(low), source);
  }

  public static NodeOperation BVEXTRACT(final int bit, final Node source) {
    return BVEXTRACT(NodeValue.newInteger(bit), source);
  }

  public static NodeOperation BVEXTRACT(final int high, final NodeValue low, final Node source) {
    return BVEXTRACT(NodeValue.newInteger(high), low, source);
  }

  public static NodeOperation BVEXTRACT(final NodeValue high, final int low, final Node source) {
    return BVEXTRACT(high, NodeValue.newInteger(low), source);
  }

  public static NodeOperation BVEXTRACT(final Node source) {
    return BVEXTRACT(source.getDataType().getSize() - 1, 0, source);
  }

  public static NodeOperation BVEXTRACT(
      final NodeValue high,
      final NodeValue low,
      final Variable source) {
    return BVEXTRACT(high, low, new NodeVariable(source));
  }

  public static NodeOperation BVEXTRACT(final NodeValue bit, final Variable source) {
    return BVEXTRACT(bit, bit, new NodeVariable(source));
  }

  public static NodeOperation BVEXTRACT(final int high, final int low, final Variable source) {
    return BVEXTRACT(
        NodeValue.newInteger(high), NodeValue.newInteger(low), new NodeVariable(source));
  }

  public static NodeOperation BVEXTRACT(final int bit, final Variable source) {
    return BVEXTRACT(NodeValue.newInteger(bit), source);
  }

  public static NodeOperation BVEXTRACT(
      final int high,
      final NodeValue low,
      final Variable source) {
    return BVEXTRACT(NodeValue.newInteger(high), low, new NodeVariable(source));
  }

  public static NodeOperation BVEXTRACT(
      final NodeValue high,
      final int low,
      final Variable source) {
    return BVEXTRACT(high, NodeValue.newInteger(low), new NodeVariable(source));
  }

  public static NodeOperation BVEXTRACT(final Variable source) {
    return BVEXTRACT(new NodeVariable(source));
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

  public static NodeOperation BVNAND(final Node first, final Node second) {
    return new NodeOperation(StandardOperation.BVNAND, first, second);
  }

  public static NodeOperation BVNOR(final Node first, final Node second) {
    return new NodeOperation(StandardOperation.BVNOR, first, second);
  }

  public static NodeOperation BVXNOR(final Node first, final Node second) {
    return new NodeOperation(StandardOperation.BVXNOR, first, second);
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

  public static NodeOperation BVANDR(final Node first, final Node second) {
    return new NodeOperation(StandardOperation.BVANDR, first, second);
  }

  public static NodeOperation BVNANDR(final Node first, final Node second) {
    return new NodeOperation(StandardOperation.BVNANDR, first, second);
  }

  public static NodeOperation BVORR(final Node first, final Node second) {
    return new NodeOperation(StandardOperation.BVORR, first, second);
  }

  public static NodeOperation BVNORR(final Node first, final Node second) {
    return new NodeOperation(StandardOperation.BVNORR, first, second);
  }

  public static NodeOperation BVXORR(final Node first, final Node second) {
    return new NodeOperation(StandardOperation.BVXORR, first, second);
  }

  public static NodeOperation BVXNORR(final Node first, final Node second) {
    return new NodeOperation(StandardOperation.BVXNORR, first, second);
  }

  public static NodeOperation BV2BOOL(final Node operand) {
    return new NodeOperation(StandardOperation.BV2BOOL, operand);
  }

  public static NodeOperation BOOL2BV(final Node operand) {
    return new NodeOperation(StandardOperation.BOOL2BV, operand);
  }

  public static NodeOperation BV2INT(final Node operand) {
    return new NodeOperation(StandardOperation.BV2INT, operand);
  }

  public static NodeOperation INT2BV(final NodeValue size, final Node source) {
    return new NodeOperation(StandardOperation.INT2BV, size, source);
  }

  public static NodeOperation INT2BV(final int size, final Node source) {
    return INT2BV(NodeValue.newInteger(size), source);
  }

  public static NodeOperation STORE(final Node array, final Node key, final Node value) {
    return new NodeOperation(StandardOperation.STORE, array, key, value);
  }

  public static NodeOperation SELECT(final Node array, final Node key) {
    return new NodeOperation(StandardOperation.SELECT, array, key);
  }
}
