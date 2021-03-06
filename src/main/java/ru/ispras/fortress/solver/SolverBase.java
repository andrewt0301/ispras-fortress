/*
 * Copyright 2013-2018 ISP RAS (http://www.ispras.ru)
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

import ru.ispras.fortress.expression.StandardOperation;
import ru.ispras.fortress.solver.constraint.ConstraintKind;
import ru.ispras.fortress.solver.function.Function;
import ru.ispras.fortress.solver.function.FunctionTemplate;
import ru.ispras.fortress.util.InvariantChecks;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

public abstract class SolverBase implements Solver {
  private static final String ERR_ALREADY_REGISTERED = "The %s.%s operation is already registered.";
  private static final String ERR_UNSUPPORTED_KIND = "Unsupported constraint type: %s.%s.";

  private final String name;
  private final String description;
  private final Set<ConstraintKind> supportedKinds;
  private final boolean isGeneric;
  private final Map<Enum<?>, SolverOperation> operations;

  private final String envVarName;
  private String solverPath;

  public SolverBase(
      final String name,
      final String description,
      final Set<ConstraintKind> supportedKinds,
      final boolean isGeneric,
      final String envVarName) {
    InvariantChecks.checkNotNull(name);
    InvariantChecks.checkNotNull(description);
    InvariantChecks.checkNotNull(supportedKinds);

    this.name = name;
    this.description = description;
    this.supportedKinds = supportedKinds;
    this.isGeneric = isGeneric;
    this.operations = new HashMap<>();

    this.envVarName = envVarName;
    this.solverPath = null;
  }

  protected final void supportedKindCheck(final ConstraintKind kind) {
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
  public final boolean isSupported(final ConstraintKind kind) {
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
  public final boolean addCustomOperation(final Function function) {
    InvariantChecks.checkNotNull(function);
    return null == operations.put(function.getId(), SolverOperation.newFunction(function));
  }

  @Override
  public final boolean addCustomOperation(final FunctionTemplate template) {
    InvariantChecks.checkNotNull(template);
    return null == operations.put(template.getId(), SolverOperation.newTemplate(template));
  }

  protected final void addStandardOperation(
      final StandardOperation id,
      final String text) {
    InvariantChecks.checkNotNull(id);
    InvariantChecks.checkNotNull(text);

    if (operations.containsKey(id)) {
      throw new IllegalArgumentException(String.format(
          ERR_ALREADY_REGISTERED, id.getClass().getSimpleName(), id.name()));
    }

    operations.put(id, SolverOperation.newText(id, text));
  }

  @Override
  public String getSolverPath() {
    if (null != solverPath) {
      return solverPath;
    }

    final String pathFromEnvVar = System.getenv(envVarName);
    if (null != pathFromEnvVar) {
      return pathFromEnvVar;
    }

    return null;
  }

  @Override
  public void setSolverPath(final String value) {
    solverPath = value;
  }
}
