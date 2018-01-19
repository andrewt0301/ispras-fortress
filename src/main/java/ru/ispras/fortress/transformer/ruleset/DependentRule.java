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

package ru.ispras.fortress.transformer.ruleset;

import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeOperation;
import ru.ispras.fortress.transformer.TransformerRule;
import ru.ispras.fortress.util.InvariantChecks;

import java.util.Collection;
import java.util.Map;

/**
 * DependentRule is a base class for rules dedicated for use in set.
 */
abstract class DependentRule implements TransformerRule {
  private final Map<Enum<?>, TransformerRule> rules;

  /**
   * Create rule for use in set.
   *
   * @param rules Ruleset shared by all interdependent rules.
   */
  protected DependentRule(final Map<Enum<?>, TransformerRule> rules) {
    InvariantChecks.checkNotNull(rules);
    this.rules = rules;
  }

  /**
   * Create expression from operation applying rules from shared set.
   *
   * @param opId Operation identifier.
   * @param operands Operation operands.
   *
   * @return Node instance which is expression resulted from recursively
   *         applying relevant rules in shared set to single operation.
   */
  protected final Node reduce(final Enum<?> opId, final Node ... operands) {
    final Node node = new NodeOperation(opId, operands);
    final TransformerRule rule = rules.get(opId);
    if (rule != null && rule.isApplicable(node)) {
      return rule.apply(node);
    }
    return node;
  }

  protected final Node reduce(final Enum<?> opId, final Collection<? extends Node> operands) {
    return reduce(opId, operands.toArray(new Node[operands.size()]));
  }
}