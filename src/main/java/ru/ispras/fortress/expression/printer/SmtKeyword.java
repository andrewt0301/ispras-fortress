/*
 * Copyright 2018 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.expression.printer;

/**
 * This class contains SMT-LIBv2 language keywords.
 *
 * @author <a href="mailto:smolov@ispras.ru">Sergey Smolov</a>
 */
public enum SmtKeyword {

  /*
   * SMT-LIB operations.
   */

  /* Logic Operations */
  EQ("="),
  NOTEQ("distinct"),
  EQCASE("="),
  NOTEQCASE("distinct"),
  AND("and"),
  OR("or"),
  NOT("not"),
  XOR("xor"),
  IMPL("=>"),
  ITE("ite"),

  // Logic arithmetic
  MINUS("-"),
  PLUS("+"),
  ADD("+"),
  SUB("-"),
  MUL("*"),
  DIV("div"),
  MOD("mod"),
  GREATER(">"),
  GREATEREQ(">="),
  LESS("<"),
  LESSEQ("<="),
  POWER("^"),

  // Basic Bitvector Arithmetic
  BVADD("bvadd"),
  BVSUB("bvsub"),
  BVNEG("bvneg"),
  BVMUL("bvmul"),
  BVUDIV("bvudiv"),
  BVSDIV("bvsdiv"),
  BVUREM("bvurem"),
  BVSREM("bvsrem"),
  BVSMOD("bvsmod"),
  BVLSHL("bvshl"),
  BVASHL("bvshl"),
  BVLSHR("bvlshr"),
  BVASHR("bvashr"),
  INT2BV("int2bv"),
  BVCONCAT("concat"),
  BVREPEAT("repeat"),
  BVEXTRACT("extract"),
  BVROL("rotate_left"),
  BVROR("rotate_right"),
  BVZEROEXT("zero_extend"),
  BVSIGNEXT("sign_extend"),

  // Bitwise Operations
  BVOR("bvor"),
  BVXOR("bvxor"),
  BVAND("bvand"),
  BVNOT("bvnot"),
  BVNAND("bvnand"),
  BVNOR("bvnor"),
  BVXNOR("bvxnor"),

  // Predicates over Bitvectors
  BVULE("bvule"),
  BVULT("bvult"),
  BVUGE("bvuge"),
  BVUGT("bvugt"),
  BVSLE("bvsle"),
  BVSLT("bvslt"),
  BVSGE("bvsge"),
  BVSGT("bvsgt"),

  /* Array operations */
  SELECT("select"),
  STORE("store");

  private String name;

  SmtKeyword(final String name) {
    this.name = name;
  }

  String getName() {
    return this.name;
  }

  /**
   * Checks that the argument is a keyword in SMT-LIB language.
   * @param word The object to be checked.
   * @return {@code true} if the argument is a keyword in a SMT-LIB language,
   *         {@code false} otherwise.
   */
  public static boolean isKeyword(final String word) {

    for (int i = 0; i < SmtKeyword.values().length; i++) {

      final SmtKeyword keyWord = SmtKeyword.values()[i];

      if (keyWord.getName().equals(word)) {
        return true;
      }
    }
    return false;
  }
}
