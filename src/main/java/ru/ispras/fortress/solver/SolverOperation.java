/*
 * Copyright 2012-2014 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.solver;

import ru.ispras.fortress.solver.function.Function;
import ru.ispras.fortress.solver.function.FunctionTemplate;
import ru.ispras.fortress.util.InvariantChecks;

/**
 * The SolverOperation class stores information about a solver operation. The information explains
 * how the operation should be translated to solver-specific representation. The SolverOperation
 * class describes both built-in and custom solver operation.
 * 
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public abstract class SolverOperation {
  /**
   * Describes the type of the solver operation.
   * 
   * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
   */
  public static enum Kind {
    TEXT, FUNCTION, TEMPLATE
  }

  private final Kind kind;
  private final Enum<?> id;

  public static final SolverOperation newText(final Enum<?> id, final String text) {
    InvariantChecks.checkNotNull(id);
    InvariantChecks.checkNotNull(text);

    return new TextOperation(id, text);
  }

  public static final SolverOperation newFunction(final Function function) {
    InvariantChecks.checkNotNull(function);
    return new FunctionOperation(function);
  }

  public static final SolverOperation newTemplate(final FunctionTemplate template) {
    InvariantChecks.checkNotNull(template);
    return new TemplateOperation(template);
  }

  /**
   * Creates a solver operation object (a custom operation).
   * 
   * @param text Textual representation of the operation.
   * @param function Definition of the operation (including its parameters and underlying
   *        expression).
   */
  private SolverOperation(final Kind kind, final Enum<?> id) {
    this.kind = kind;
    this.id = id;
  }

  /**
   * Returns information of the type of the operation.
   * 
   * @return Operation kind.
   */
  public final Kind getKind() {
    return kind;
  }

  /**
   * Returns the textual representation of the operation.
   * 
   * @return Textual representation of the operation.
   */
  public final Enum<?> getOperationId() {
    return id;
  }

  public abstract String getText();

  /**
   * Returns the underlying function.
   * 
   * @return Underlying function.
   */
  public abstract Function getFunction();

  /**
   * Returns the underlying function template.
   * 
   * @return Underlying function template.
   */
  public abstract FunctionTemplate getTemplate();

  private static class TextOperation extends SolverOperation {
    private final String text;

    private TextOperation(final Enum<?> id, final String text) {
      super(Kind.TEXT, id);
      this.text = text;
    }

    @Override
    public String getText() {
      return text;
    }

    @Override
    public Function getFunction() {
      return null;
    }

    @Override
    public FunctionTemplate getTemplate() {
      return null;
    }
  }

  private static class FunctionOperation extends SolverOperation {
    private final Function function;

    private FunctionOperation(final Function function) {
      super(Kind.FUNCTION, function.getId());
      this.function = function;
    }

    @Override
    public String getText() {
      return function.getUniqueName();
    }

    @Override
    public Function getFunction() {
      return function;
    }

    @Override
    public FunctionTemplate getTemplate() {
      return null;
    }
  }

  private static class TemplateOperation extends SolverOperation {
    private final FunctionTemplate template;

    private TemplateOperation(final FunctionTemplate template) {
      super(Kind.TEMPLATE, template.getId());
      this.template = template;
    }

    @Override
    public String getText() {
      return null;
    }

    @Override
    public Function getFunction() {
      return null;
    }

    @Override
    public FunctionTemplate getTemplate() {
      return template;
    }
  }
}
