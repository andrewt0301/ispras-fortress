/*
 * Copyright 2017-2018 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.transformer;

import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.util.InvariantChecks;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * Aggregate of rules to be used in {@link NodeTransformer} when multiple
 * rules per operation required. Rules are checked in sequential order.
 */
public class CompositeRule implements TransformerRule {
  private final List<TransformerRule> rules;

  private Node nodeCache = null;
  private TransformerRule ruleCache = null;

  public CompositeRule(final List<? extends TransformerRule> rules) {
    InvariantChecks.checkNotNull(rules);
    if (rules.isEmpty()) {
      this.rules = Collections.emptyList();
    } else {
      this.rules = new ArrayList<>(rules);
    }
  }

  @Override
  public boolean isApplicable(final Node node) {
    InvariantChecks.checkNotNull(node);
    final TransformerRule rule = findRule(node);
    if (rule != null) {
      nodeCache = node;
      ruleCache = rule;
      return true;
    }
    return false;
  }

  @Override
  public Node apply(final Node node) {
    InvariantChecks.checkNotNull(node);
    final TransformerRule rule = (nodeCache == node) ? ruleCache : findRule(node);
    if (rule != null) {
      return rule.apply(node);
    }
    return node;
  }

  private TransformerRule findRule(final Node node) {
    for (final TransformerRule rule : rules) {
      if (rule.isApplicable(node)) {
        return rule;
      }
    }
    return null;
  }
}
