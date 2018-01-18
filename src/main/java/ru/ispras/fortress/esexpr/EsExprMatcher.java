/*
 * Copyright 2014-2018 ISP RAS (http://www.ispras.ru)
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

import ru.ispras.fortress.util.InvariantChecks;

/**
 * The {@link EsExprMatcher} is expression structure matcher for {@link EsExpr}.
 * Matches expressions with patterns as-is, i.e. without normalization,
 * respecting expression structure.
 * Uses same Lisp-syntax notation for pattern specification, supports
 * several wildcards: {@code %a} matches any atom including {@code NIL},
 * {@code %s} matches any S-expression.
 */
public final class EsExprMatcher {
  private static final String ATOM = "%a";
  private static final String SEXPR = "%s";

  private final EsExpr pattern;

  /**
   * Create new matcher for given pattern.
   *
   * @param pattern Lisp-syntax S-expression denoting pattern to match
   * @throws IllegalArgumentException if {@code pattern} is {@code null}
   */
  public EsExprMatcher(String pattern) {
    InvariantChecks.checkNotNull(pattern);

    EsExpr sexpr = EsExpr.NIL;
    try {
      final EsExprParser parser = EsExprParser.stringParser(pattern);
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
   * @param expr S-expression to be checked for match
   * @return {@code true} if given expression matches
   * @throws IllegalArgumentException if {@code e} is {@code null}
   */
  public boolean matches(EsExpr expr) {
    InvariantChecks.checkNotNull(expr);
    return matches(expr, pattern);
  }

  /**
   * Returns {@code true} if given expression matches given pattern.
   *
   * @param expr S-expression to be checked for match
   * @param pattern S-expression denoting pattern
   * @return {@code true} if given expression matches
   */
  private static boolean matches(EsExpr expr, EsExpr pattern) {
    if (pattern.getLiteral().equals(SEXPR)) {
      return true;
    }
    if (pattern.getLiteral().equals(ATOM)) {
      return expr.isAtom();
    }
    if (pattern.isAtom()) {
      return expr.isAtom() && expr.getLiteral().equals(pattern.getLiteral());
    }
    if (expr.getItems().size() != pattern.getItems().size()) {
      return false;
    }
    for (int i = 0; i < expr.getItems().size(); ++i) {
      if (!matches(expr.getItems().get(i), pattern.getItems().get(i))) {
        return false;
      }
    }
    return true;
  }
}
