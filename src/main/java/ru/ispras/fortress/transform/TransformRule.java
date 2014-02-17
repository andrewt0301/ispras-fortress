package ru.ispras.fortress.transform;

import ru.ispras.fortress.expression.Node;

public interface TransformRule
{
    boolean isApplicable(Node node);
    Node apply(Node node);
}
