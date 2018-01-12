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

import ru.ispras.fortress.util.InvariantChecks;

import java.io.IOException;
import java.io.BufferedReader;
import java.io.Reader;
import java.io.StreamTokenizer;
import java.io.StringReader;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;

/**
 * ESExprParser translates Lisp-like syntax into {@link ESExpr}.
 * Supports only ASCII characters, treats ';' as start of one-line comment,
 * does not support multiline symbols and treats them as sequence of expressions.
 */
public final class ESExprParser {
  private final StreamTokenizer tokenizer;
  private final Deque<List<ESExpr>> stack;

  /**
   * Create new parser for given reader.
   *
   * @param reader {@code Reader} instance to read input from
   */
  public ESExprParser(final Reader reader) {
    InvariantChecks.checkNotNull(reader);

    final BufferedReader buf = new BufferedReader(reader);
    final StringBuilder txt = new StringBuilder();
    try {
      for (String line = buf.readLine(); line != null; line = buf.readLine()) {
        txt.append(line);
        txt.append(' ');
      }
    } catch (final IOException e) {
      txt.append(String.format("(error \"%s\")", e.getMessage()));
    }

    this.tokenizer = setUpTokenizer(new StringReader(txt.toString()));
    this.stack = new ArrayDeque<>();
  }

  /**
   * Returns next complete S-expression read from input.
   *
   * @return complete S-expression
   */
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

  /**
   * Reads current tuple elements til the end of tuple.
   *
   * @return {@code true} if elements been read are given in dot notation
   * @throws IllegalArgumentException if parsing error occurred
   */
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

  /**
   * Read next token from input stream. Workaround StreamTokenizer to treat
   * standalone '.' (dot) atoms as separate tokens.
   *
   * @return token been read.
   * @throws  IOException if an I/O error occurs.
   */
  private int nextToken() throws IOException {
    final int token = tokenizer.nextToken();
    if (token == StreamTokenizer.TT_WORD && tokenizer.sval.equals(".")) {
      return '.';
    }
    return token;
  }

  /**
   * Returns {@code true} if at least two elements of current tuple has
   * been read. I.e. if list-syntax and dot-syntax can be distinguished.
   */
  private boolean delimiterFound() {
    return !stack.isEmpty() && stack.peek().size() > 1;
  }

  /**
   * Creates parser for given string.
   *
   * @param s string to parse
   * @return parser for given string
   * @throws IllegalArgumentException if {@code s} is {@code null}
   */
  public static ESExprParser stringParser(final String s) {
    InvariantChecks.checkNotNull(s);
    return new ESExprParser(new StringReader(s));
  }

  /**
   * Create and properly set up StreamTokenizer
   *
   * @param reader {@code Reader} instance to read input from
   * @return tokenizer for given input reader
   */
  private static StreamTokenizer setUpTokenizer(final Reader reader) {
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
