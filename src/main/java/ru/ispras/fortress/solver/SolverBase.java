/*
 * Copyright 2013-2014 ISP RAS (http://www.ispras.ru)
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

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.solver.constraint.ConstraintKind;
import ru.ispras.fortress.solver.function.Function;
import ru.ispras.fortress.solver.function.FunctionTemplate;

public abstract class SolverBase implements Solver {
  private static final String ERR_ALREADY_REGISTERED = "The %s.%s operation is already registered.";
  private static final String ERR_UNSUPPORTED_KIND = "Unsupported constraint type: %s.%s.";

  private final String name;
  private final String description;
  private final Set<ConstraintKind> supportedKinds;
  private final boolean isGeneric;
  private final Map<Enum<?>, SolverOperation> operations;

  public SolverBase(String name, String description, Set<ConstraintKind> supportedKinds,
      boolean isGeneric) {
    notNullCheck(name, "name");
    notNullCheck(description, "description");
    notNullCheck(supportedKinds, "supportedKinds");

    this.name = name;
    this.description = description;
    this.supportedKinds = supportedKinds;
    this.isGeneric = isGeneric;
    this.operations = new HashMap<Enum<?>, SolverOperation>();
  }

  protected static void notNullCheck(Object o, String name) {
    if (null == o) {
      throw new NullPointerException(name + " is null");
    }
  }

  protected final void supportedKindCheck(ConstraintKind kind) {
    if (!isSupported(kind)) {
      throw new IllegalArgumentException(String.format(
        ERR_UNSUPPORTED_KIND, kind.getClass().getSimpleName(), kind));
    }
  }

  @Override
  public final String getName() {
    return name;
  }

  @Override
  public final String getDescription() {
    return description;
  }

  @Override
  public final boolean isSupported(ConstraintKind kind) {
    return supportedKinds.contains(kind);
  }

  @Override
  public final boolean isGeneric() {
    return isGeneric;
  }

  public final Map<Enum<?>, SolverOperation> getOperations() {
    return Collections.unmodifiableMap(operations);
  }

  @Override
  public final boolean addCustomOperation(Function function) {
    notNullCheck(function, "function");
    return null == operations.put(function.getId(), SolverOperation.newFunction(function));
  }

  @Override
  public final boolean addCustomOperation(FunctionTemplate template) {
    notNullCheck(template, "template");
    return null == operations.put(template.getId(), SolverOperation.newTemplate(template));
  }

  protected final void addStandardOperation(StandardOperation id, String text) {
    notNullCheck(id, "id");
    notNullCheck(text, "text");

    if (operations.containsKey(id)) {
      throw new IllegalArgumentException(String.format(
        ERR_ALREADY_REGISTERED, id.getClass().getSimpleName(), id.name()));
    }

    operations.put(id, SolverOperation.newText(id, text));
  }
}
