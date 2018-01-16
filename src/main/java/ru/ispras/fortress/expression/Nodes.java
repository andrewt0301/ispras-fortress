/*
 * Copyright 2017-2018 ISP RAS (http://www.ispras.ru)
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

import ru.ispras.fortress.data.Variable;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
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

  public static NodeOperation eq(final Node lhs, final Node rhs) {
    return new NodeOperation(StandardOperation.EQ, lhs, rhs);
  }

  public static NodeOperation eq(final Variable lhs, final Node rhs) {
    return eq(new NodeVariable(lhs), rhs);
  }

  public static NodeOperation eq(final Node lhs, final Variable rhs) {
    return eq(lhs, new NodeVariable(rhs));
  }

  public static NodeOperation noteq(final Node lhs, final Node rhs) {
    return new NodeOperation(StandardOperation.NOTEQ, lhs, rhs);
  }

  public static NodeOperation noteq(final Variable lhs, final Node rhs) {
    return noteq(new NodeVariable(lhs), rhs);
  }

  public static NodeOperation noteq(final Node lhs, final Variable rhs) {
    return noteq(lhs, new NodeVariable(rhs));
  }

  public static NodeOperation eqcase(final Node lhs, final Node rhs) {
    return new NodeOperation(StandardOperation.EQCASE, lhs, rhs);
  }

  public static NodeOperation noteqcase(final Node lhs, final Node rhs) {
    return new NodeOperation(StandardOperation.NOTEQCASE, lhs, rhs);
  }

  public static NodeOperation and(final Node... operands) {
    return new NodeOperation(StandardOperation.AND, operands);
  }

  public static NodeOperation and(final List<? extends Node> operands) {
    return new NodeOperation(StandardOperation.AND, operands);
  }

  public static NodeOperation or(final Node... operands) {
    return new NodeOperation(StandardOperation.OR, operands);
  }

  public static NodeOperation or(final List<? extends Node> operands) {
    return new NodeOperation(StandardOperation.OR, operands);
  }

  public static NodeOperation not(final Node operand) {
    return new NodeOperation(StandardOperation.NOT, operand);
  }

  public static NodeOperation xor(final Node... operands) {
    return new NodeOperation(StandardOperation.XOR, operands);
  }

  public static NodeOperation xor(final List<? extends Node> operands) {
    return new NodeOperation(StandardOperation.XOR, operands);
  }

  public static NodeOperation impl(final Node first, final Node second) {
    return new NodeOperation(StandardOperation.IMPL, first, second);
  }

  public static NodeOperation ite(final Node condition, final Node first, final Node second) {
    return new NodeOperation(StandardOperation.ITE, condition, first, second);
  }

  public static NodeOperation minus(final Node operand) {
    return new NodeOperation(StandardOperation.MINUS, operand);
  }

  public static NodeOperation plus(final Node operand) {
    return new NodeOperation(StandardOperation.PLUS, operand);
  }

  public static NodeOperation add(final Node... operands) {
    return new NodeOperation(StandardOperation.ADD, operands);
  }

  public static NodeOperation add(final List<? extends Node> operands) {
    return new NodeOperation(StandardOperation.ADD, operands);
  }

  public static NodeOperation sub(final Node... operands) {
    return new NodeOperation(StandardOperation.SUB, operands);
  }

  public static NodeOperation sub(final List<? extends Node> operands) {
    return new NodeOperation(StandardOperation.SUB, operands);
  }

  public static NodeOperation div(final Node first, final Node second) {
    return new NodeOperation(StandardOperation.DIV, first, second);
  }

  public static NodeOperation mul(final Node... operands) {
    return new NodeOperation(StandardOperation.MUL, operands);
  }

  public static NodeOperation mul(final List<? extends Node> operands) {
    return new NodeOperation(StandardOperation.MUL, operands);
  }

  public static NodeOperation rem(final Node first, final Node second) {
    return new NodeOperation(StandardOperation.REM, first, second);
  }

  public static NodeOperation mod(final Node first, final Node second) {
    return new NodeOperation(StandardOperation.MOD, first, second);
  }

  public static NodeOperation less(final Node lhs, final Node rhs) {
    return new NodeOperation(StandardOperation.LESS, lhs, rhs);
  }

  public static NodeOperation lesseq(final Node lhs, final Node rhs) {
    return new NodeOperation(StandardOperation.LESSEQ, lhs, rhs);
  }

  public static NodeOperation greater(final Node lhs, final Node rhs) {
    return new NodeOperation(StandardOperation.GREATER, lhs, rhs);
  }

  public static NodeOperation greatereq(final Node lhs, final Node rhs) {
    return new NodeOperation(StandardOperation.GREATEREQ, lhs, rhs);
  }

  public static NodeOperation power(final Node base, final Node exponent) {
    return new NodeOperation(StandardOperation.POWER, base, exponent);
  }

  public static NodeOperation abs(final Node operand) {
    return new NodeOperation(StandardOperation.ABS, operand);
  }

  public static NodeOperation min(final Node... operands) {
    return new NodeOperation(StandardOperation.MIN, operands);
  }

  public static NodeOperation min(final List<? extends Node> operands) {
    return new NodeOperation(StandardOperation.MIN, operands);
  }

  public static NodeOperation max(final Node... operands) {
    return new NodeOperation(StandardOperation.MAX, operands);
  }

  public static NodeOperation max(final List<? extends Node> operands) {
    return new NodeOperation(StandardOperation.MAX, operands);
  }

  public static NodeOperation bvadd(final Node... operands) {
    return new NodeOperation(StandardOperation.BVADD, operands);
  }

  public static NodeOperation bvadd(final List<? extends Node> operands) {
    return new NodeOperation(StandardOperation.BVADD, operands);
  }

  public static NodeOperation bvsub(final Node... operands) {
    return new NodeOperation(StandardOperation.BVSUB, operands);
  }

  public static NodeOperation bvsub(final List<? extends Node> operands) {
    return new NodeOperation(StandardOperation.BVSUB, operands);
  }

  public static NodeOperation bvneg(final Node operand) {
    return new NodeOperation(StandardOperation.BVNEG, operand);
  }

  public static NodeOperation bvmul(final Node... operands) {
    return new NodeOperation(StandardOperation.BVMUL, operands);
  }

  public static NodeOperation bvmul(final List<? extends Node> operands) {
    return new NodeOperation(StandardOperation.BVMUL, operands);
  }

  public static NodeOperation bvudiv(final Node first, final Node second) {
    return new NodeOperation(StandardOperation.BVUDIV, first, second);
  }

  public static NodeOperation bvsdiv(final Node first, final Node second) {
    return new NodeOperation(StandardOperation.BVSDIV, first, second);
  }

  public static NodeOperation bvurem(final Node first, final Node second) {
    return new NodeOperation(StandardOperation.BVUREM, first, second);
  }

  public static NodeOperation bvsrem(final Node first, final Node second) {
    return new NodeOperation(StandardOperation.BVSREM, first, second);
  }

  public static NodeOperation bvsmod(final Node first, final Node second) {
    return new NodeOperation(StandardOperation.BVSMOD, first, second);
  }

  public static NodeOperation bvlshl(final Node source, final Node amount) {
    return new NodeOperation(StandardOperation.BVLSHL, source, amount);
  }

  public static NodeOperation bvashl(final Node source, final Node amount) {
    return new NodeOperation(StandardOperation.BVASHL, source, amount);
  }

  public static NodeOperation bvlshr(final Node source, final Node amount) {
    return new NodeOperation(StandardOperation.BVLSHR, source, amount);
  }

  public static NodeOperation bvashr(final Node source, final Node amount) {
    return new NodeOperation(StandardOperation.BVASHR, source, amount);
  }

  // Operands: [HIGH, ... , LOW]
  public static NodeOperation bvconcat(final Node... operands) {
    return new NodeOperation(StandardOperation.BVCONCAT, operands);
  }

  // Operands: [HIGH, ... , LOW]
  public static NodeOperation bvconcat(final List<? extends Node> operands) {
    return new NodeOperation(StandardOperation.BVCONCAT, operands);
  }

  // Operands: [LOW, ... , HIGH]
  public static NodeOperation reverseBvconcat(final Node... operands) {
    return reverseBvconcat(Arrays.asList(operands));
  }

  // Operands: [LOW, ... , HIGH]
  public static NodeOperation reverseBvconcat(final List<? extends Node> operands) {
    final List<Node> reversedOperands = new ArrayList<>(operands);
    Collections.reverse(reversedOperands);
    return bvconcat(reversedOperands);
  }

  public static NodeOperation bvrepeat(final NodeValue count, final Node source) {
    return new NodeOperation(StandardOperation.BVREPEAT, count, source);
  }

  public static NodeOperation bvrepeat(final int count, final Node source) {
    return new NodeOperation(StandardOperation.BVREPEAT, NodeValue.newInteger(count), source);
  }

  public static NodeOperation bvrol(final NodeValue amount, final Node source) {
    return new NodeOperation(StandardOperation.BVROL, amount, source);
  }

  public static NodeOperation bvrol(final int amount, final Node source) {
    return bvrol(NodeValue.newInteger(amount), source);
  }

  public static NodeOperation bvror(final NodeValue amount, final Node source) {
    return new NodeOperation(StandardOperation.BVROR, amount, source);
  }

  public static NodeOperation bvror(final int amount, final Node source) {
    return bvror(NodeValue.newInteger(amount), source);
  }

  public static NodeOperation bvzeroext(final NodeValue deltaSize, final Node source) {
    return new NodeOperation(StandardOperation.BVZEROEXT, deltaSize, source);
  }

  public static NodeOperation bvzeroext(final int deltaSize, final Node source) {
    return bvzeroext(NodeValue.newInteger(deltaSize), source);
  }

  public static NodeOperation bvsignext(final NodeValue deltaSize, final Node source) {
    return new NodeOperation(StandardOperation.BVSIGNEXT, deltaSize, source);
  }

  public static NodeOperation bvsignext(final int deltaSize, final Node source) {
    return bvsignext(NodeValue.newInteger(deltaSize), source);
  }

  public static NodeOperation bvextract(
      final NodeValue high,
      final NodeValue low,
      final Node source) {
    return new NodeOperation(StandardOperation.BVEXTRACT, high, low, source);
  }

  public static NodeOperation bvextract(final NodeValue bit, final Node source) {
    return bvextract(bit, bit, source);
  }

  public static NodeOperation bvextract(final int high, final int low, final Node source) {
    return bvextract(NodeValue.newInteger(high), NodeValue.newInteger(low), source);
  }

  public static NodeOperation bvextract(final int bit, final Node source) {
    return bvextract(NodeValue.newInteger(bit), source);
  }

  public static NodeOperation bvextract(final int high, final NodeValue low, final Node source) {
    return bvextract(NodeValue.newInteger(high), low, source);
  }

  public static NodeOperation bvextract(final NodeValue high, final int low, final Node source) {
    return bvextract(high, NodeValue.newInteger(low), source);
  }

  public static NodeOperation bvextract(final Node source) {
    return bvextract(source.getDataType().getSize() - 1, 0, source);
  }

  public static NodeOperation bvextract(
      final NodeValue high,
      final NodeValue low,
      final Variable source) {
    return bvextract(high, low, new NodeVariable(source));
  }

  public static NodeOperation bvextract(final NodeValue bit, final Variable source) {
    return bvextract(bit, bit, new NodeVariable(source));
  }

  public static NodeOperation bvextract(final int high, final int low, final Variable source) {
    return bvextract(
        NodeValue.newInteger(high), NodeValue.newInteger(low), new NodeVariable(source));
  }

  public static NodeOperation bvextract(final int bit, final Variable source) {
    return bvextract(NodeValue.newInteger(bit), source);
  }

  public static NodeOperation bvextract(
      final int high,
      final NodeValue low,
      final Variable source) {
    return bvextract(NodeValue.newInteger(high), low, new NodeVariable(source));
  }

  public static NodeOperation bvextract(
      final NodeValue high,
      final int low,
      final Variable source) {
    return bvextract(high, NodeValue.newInteger(low), new NodeVariable(source));
  }

  public static NodeOperation bvextract(final Variable source) {
    return bvextract(new NodeVariable(source));
  }

  public static NodeOperation bvor(final Node... operands) {
    return new NodeOperation(StandardOperation.BVOR, operands);
  }

  public static NodeOperation bvor(final List<? extends Node> operands) {
    return new NodeOperation(StandardOperation.BVOR, operands);
  }

  public static NodeOperation bvxor(final Node... operands) {
    return new NodeOperation(StandardOperation.BVXOR, operands);
  }

  public static NodeOperation bvxor(final List<? extends Node> operands) {
    return new NodeOperation(StandardOperation.BVXOR, operands);
  }

  public static NodeOperation bvand(final Node... operands) {
    return new NodeOperation(StandardOperation.BVAND, operands);
  }

  public static NodeOperation bvand(final List<? extends Node> operands) {
    return new NodeOperation(StandardOperation.BVAND, operands);
  }

  public static NodeOperation bvnot(final Node operand) {
    return new NodeOperation(StandardOperation.BVNOT, operand);
  }

  public static NodeOperation bvnand(final Node first, final Node second) {
    return new NodeOperation(StandardOperation.BVNAND, first, second);
  }

  public static NodeOperation bvnor(final Node first, final Node second) {
    return new NodeOperation(StandardOperation.BVNOR, first, second);
  }

  public static NodeOperation bvxnor(final Node first, final Node second) {
    return new NodeOperation(StandardOperation.BVXNOR, first, second);
  }

  public static NodeOperation bvule(final Node lhs, final Node rhs) {
    return new NodeOperation(StandardOperation.BVULE, lhs, rhs);
  }

  public static NodeOperation bvult(final Node lhs, final Node rhs) {
    return new NodeOperation(StandardOperation.BVULT, lhs, rhs);
  }

  public static NodeOperation bvuge(final Node lhs, final Node rhs) {
    return new NodeOperation(StandardOperation.BVUGE, lhs, rhs);
  }

  public static NodeOperation bvugt(final Node lhs, final Node rhs) {
    return new NodeOperation(StandardOperation.BVUGT, lhs, rhs);
  }

  public static NodeOperation bvsle(final Node lhs, final Node rhs) {
    return new NodeOperation(StandardOperation.BVSLE, lhs, rhs);
  }

  public static NodeOperation bvslt(final Node lhs, final Node rhs) {
    return new NodeOperation(StandardOperation.BVSLT, lhs, rhs);
  }

  public static NodeOperation bvsge(final Node lhs, final Node rhs) {
    return new NodeOperation(StandardOperation.BVSGE, lhs, rhs);
  }

  public static NodeOperation bvsgt(final Node lhs, final Node rhs) {
    return new NodeOperation(StandardOperation.BVSGT, lhs, rhs);
  }

  public static NodeOperation bvandr(final Node operand) {
    return new NodeOperation(StandardOperation.BVANDR, operand);
  }

  public static NodeOperation bvnandr(final Node operand) {
    return new NodeOperation(StandardOperation.BVNANDR, operand);
  }

  public static NodeOperation bvorr(final Node operand) {
    return new NodeOperation(StandardOperation.BVORR, operand);
  }

  public static NodeOperation bvnorr(final Node operand) {
    return new NodeOperation(StandardOperation.BVNORR, operand);
  }

  public static NodeOperation bvxorr(final Node operand) {
    return new NodeOperation(StandardOperation.BVXORR, operand);
  }

  public static NodeOperation bvxnorr(final Node operand) {
    return new NodeOperation(StandardOperation.BVXNORR, operand);
  }

  public static NodeOperation bv2bool(final Node operand) {
    return new NodeOperation(StandardOperation.BV2BOOL, operand);
  }

  public static NodeOperation bool2bv(final Node operand) {
    return new NodeOperation(StandardOperation.BOOL2BV, operand);
  }

  public static NodeOperation bv2int(final Node operand) {
    return new NodeOperation(StandardOperation.BV2INT, operand);
  }

  public static NodeOperation int2bv(final NodeValue size, final Node source) {
    return new NodeOperation(StandardOperation.INT2BV, size, source);
  }

  public static NodeOperation int2bv(final int size, final Node source) {
    return int2bv(NodeValue.newInteger(size), source);
  }

  public static NodeOperation store(final Node array, final Node key, final Node value) {
    return new NodeOperation(StandardOperation.STORE, array, key, value);
  }

  public static NodeOperation select(final Node array, final Node key) {
    return new NodeOperation(StandardOperation.SELECT, array, key);
  }
}
