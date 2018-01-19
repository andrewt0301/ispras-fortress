/*
 * Copyright 2015 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.util;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * The {@link Result} class is base class for describing results of some complex calculations.
 * Includes status enumeration, result object and a list of error messages.
 *
 * @param <E> Type of the status enumeration.
 * @param <T> Type of the result object.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public class Result<E extends Enum<E>, T> {
  private final E status;
  private final T result;
  private final List<String> errors;

  /**
   * Constructs a {@link Result} object on the basis of status, object representing the result
   * and the list of error messages.
   *
   * @param status Status enumeration item.
   * @param result Result object.
   * @param errors List of error messages.
   *
   * @throws IllegalArgumentException if the {@code status} or {@code errors} argument
   *         is {@code null}.
   */
  public Result(final E status, final T result, final List<String> errors) {
    InvariantChecks.checkNotNull(status);
    InvariantChecks.checkNotNull(errors);

    this.status = status;
    this.result = result;
    this.errors = Collections.unmodifiableList(new ArrayList<>(errors));
  }

  public final E getStatus() {
    return status;
  }

  public final T getResult() {
    return result;
  }

  public final boolean hasErrors() {
    return !errors.isEmpty();
  }

  public final List<String> getErrors() {
    return errors;
  }

  @Override
  public String toString() {
    return String.format(
        "Result [status=%s, result=%s, errors=%s]",
        status,
        result,
        errors
        );
  }
}
