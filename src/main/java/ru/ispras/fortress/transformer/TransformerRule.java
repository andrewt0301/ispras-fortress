/*
 * Copyright 2014 ISP RAS (http://www.ispras.ru)
 * 
 * Licensed under the Apache License, Version 2.0 (the "License"); you may
 * not use this file except in compliance with the License. You may obtain
 * a copy of the License at
 * 
 * http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package ru.ispras.fortress.transformer;

import ru.ispras.fortress.expression.Node;

/**
 *  The TransformerRule is an interface to be implemented by all rules
 *  being used in {@link NodeTransformer}.
 */

public interface TransformerRule
{
    /**
     *  Test for the rule can be applied to given node.
     *
     *  @param node Expression node to check applicability for.
     *  @return true if the rule is applicable to given node.
     */

    boolean isApplicable(Node node);

    /**
     *  Apply the rule to given node (when applicable).
     *
     *  @return Node substitution expression.
     */

    Node apply(Node node);
}
