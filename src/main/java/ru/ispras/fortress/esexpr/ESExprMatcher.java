package ru.ispras.fortress.esexpr;

public final class ESExprMatcher {
  private static final String ATOM = "%a";
  private static final String SEXPR = "%s";

  final ESExpr pattern;

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

  public boolean matches(ESExpr e) {
    return matches(e, pattern);
  }

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
