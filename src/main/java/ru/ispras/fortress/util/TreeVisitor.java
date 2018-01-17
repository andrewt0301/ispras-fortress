/*
 * Copyright 2016-2018 ISP RAS (http://www.ispras.ru)
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

/**
 * The {@link TreeVisitor} interface is to be implemented by all visitor objects
 * that are applied to hierarchical (tree-like or forest-like) structures to collect
 * information or to perform transformations. The interface describes the protocol for
 * traversal of hierarchical structures. The general idea is:
 * 
 * <p>Traversal of hierarchical structures starts with calling the {@code onBegin}
 * method and ends with calling the {@code onEnd} methods. Likewise, traversal of
 * any non-terminal node of the structure starts with calling a method with
 * the {@code Begin} suffix and ends with calling a method with the {@code End} suffix.
 * 
 * <p>Steps taken in the traversal process depend on the current status of the
 * visitor (see {@link Status}). There are three possible statuses:
 * <ol>
 * <li>{@code OK} - continue traversal;
 * <li>{@code SKIP} - skip child nodes;
 * <li>{@code ABORT} - stop traversal.
 * </ol>
 * 
 * <p>The status is checked after calling any visitor method. Once {@code ABORT} is set,
 * all traversal methods return. If after a call to a method having the {@code Begin} suffix,
 * the {@code SKIP} status is set (not {@code ABORT} and not {@code OK}), nested elements of
 * the visited node (child nodes or subtrees) are not traversed and a corresponding
 * terminating method (that has the {@code End} suffix) is called.
 * 
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public interface TreeVisitor {
  /**
   * The {@link Status} enumeration describes possible statuses of the visitor.
   * {@code Status} serves as a directive for the walker to alter its behavior
   * depending on events that may occur in the visitor.
   * 
   * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
   */
  static enum Status {

    /**
     * Continue traversing.
     */
    OK,

    /**
     * Skip child nodes.
     */
    SKIP,

    /**
     * Stop traversing.
     */
    ABORT
  }

  /**
   * Returns the current status of the visitor. The status guides further
   * actions of the walker.
   * 
   * @return Current visitor status.
   */
  Status getStatus();

  /**
   * Notifies that processing of a hierarchical structure has been started.
   */
  void onBegin();

  /**
   * Notifies that processing of a hierarchical structure has been finished.
   */
  void onEnd();
}

