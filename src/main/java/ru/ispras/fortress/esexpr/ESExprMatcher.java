/*
 * Copyright 2014 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.esexpr;

/**
 * The ESExprMatcher is expression structure matcher for {@link ESExpr}.
 * Matches expressions with patterns as-is, i.e. without normalization,
 * respecting expression structure.
 * Uses same Lisp-syntax notation for pattern specification, supports
 * several wildcards: {@code %a} matches any atom including {@code NIL},
 * {@code %s} matches any S-expression.
 */

public final class ESExprMatcher {
  private static final String ATOM = "%a";
  private static final String SEXPR = "%s";

  final ESExpr pattern;

  /**
   * Create new matcher for given pattern.
   *
   * @param pattern Lisp-syntax S-expression denoting pattern to match
   * @throws NullPointerException if {@code pattern} is {@code null}
   */

  public ESExprMatcher(String pattern) {
    if (pattern == null) {
      throw new NullPointerException();
    }
    ESExpr sexpr = ESExpr.NIL;
    try {
      final ESExprParser parser = ESExprParser.stringParser(pattern);
      sexpr = parser.next();
    } catch (java.io.IOException e) {
      System.err.println(e.getMessage());
      assert false;
    }
    this.pattern = sexpr;
  }

  /**
   * Returns {@code true} if given expression matches this matcher.
   *
   * @param e S-expression to be checked for match
   * @return {@code true} if given expression matches
   * @throws NullPointerException if {@code e} is {@code null}
   */

  public boolean matches(ESExpr e) {
    if (e == null) {
      throw new NullPointerException();
    }
    return matches(e, pattern);
  }

  /**
   * Returns {@code true} if given expression matches given pattern.
   *
   * @param e S-expression to be checked for match
   * @param pattern S-expression denoting pattern
   * @return {@code true} if given expression matches
   */

  private static boolean matches(ESExpr e, ESExpr pattern) {
    if (pattern.getLiteral().equals(SEXPR)) {
      return true;
    }
    if (pattern.getLiteral().equals(ATOM)) {
      return e.isAtom();
    }
    if (pattern.isAtom()) {
      return e.isAtom() && e.getLiteral().equals(pattern.getLiteral());
    }
    if (e.getItems().size() != pattern.getItems().size()) {
      return false;
    }
    for (int i = 0; i < e.getItems().size(); ++i) {
      if (!matches(e.getItems().get(i), pattern.getItems().get(i))) {
        return false;
      }
    }
    return true;
  }
}
