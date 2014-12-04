package ru.ispras.fortress.esexpr;

import java.io.IOException;
import java.io.Reader;
import java.io.StreamTokenizer;
import java.io.StringReader;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;

public final class ESExprParser {
  final StreamTokenizer tokenizer;
  final Deque<List<ESExpr>> stack;

  public ESExprParser(Reader reader) {
    if (reader == null) {
      throw new NullPointerException();
    }
    this.tokenizer = setUpTokenizer(reader);
    this.stack = new ArrayDeque<>();
  }

  public ESExpr next() throws IOException {
    final int token = nextToken();
    switch (token) {
      case '"':
      case StreamTokenizer.TT_WORD:
        return ESExpr.createAtom(tokenizer.sval);

      case '(':
        stack.push(new ArrayList<ESExpr>());
        if (!readItems()) {
          return ESExpr.createList(stack.pop());
        }
        return ESExpr.createTuple(stack.pop());

      case StreamTokenizer.TT_EOF:
        return null;

      default:
        throw new IllegalArgumentException("Malformed string S-expr: " + tokenizer);
    }
  }

  private boolean readItems() throws IOException {
    boolean dotted = false;
    int token = nextToken();
    while (token != ')') {
      if (token == StreamTokenizer.TT_EOF) {
        throw new IllegalArgumentException("Malformed string S-expr: " + tokenizer);
      }
      tokenizer.pushBack();
      stack.peek().add(this.next());

      token = nextToken();
      if (token == '.') {
        if (!delimiterFound()) {
          dotted = true;
        } else if (!dotted) {
          throw new IllegalArgumentException("Mixing dot and list notations: " + tokenizer);
        }
        token = nextToken();
      } else if (dotted && token != ')') {
        throw new IllegalArgumentException("Mixing dot and list notations: " + tokenizer);
      }
    }
    return dotted;
  }

  private int nextToken() throws IOException {
    final int token = tokenizer.nextToken();
    if (token == StreamTokenizer.TT_WORD && tokenizer.sval.equals(".")) {
      return '.';
    }
    return token;
  }

  private boolean delimiterFound() {
    return !stack.isEmpty() && stack.peek().size() > 1;
  }

  public static ESExprParser stringParser(String s) {
    if (s == null) {
      throw new NullPointerException();
    }
    return new ESExprParser(new StringReader(s));
  }

  private static StreamTokenizer setUpTokenizer(Reader reader) {
    final StreamTokenizer tokenizer = new StreamTokenizer(reader);
    tokenizer.resetSyntax();

    tokenizer.wordChars(33, 126);

    tokenizer.quoteChar('"');
    // tokenizer.quoteChar('|'); FIXME multiline symbols
    tokenizer.commentChar(';');

    tokenizer.ordinaryChar('(');
    tokenizer.ordinaryChar(')');

    tokenizer.whitespaceChars(' ', ' ');
    tokenizer.whitespaceChars('\n', '\n');
    tokenizer.whitespaceChars('\t', '\t');
    tokenizer.whitespaceChars('\r', '\r');

    tokenizer.eolIsSignificant(false);

    return tokenizer;
  }
}
