package ru.ispras.fortress.transformer;

import ru.ispras.fortress.expression.Node;

public interface TransformerRule
{
    boolean isApplicable(Node node);
    Node apply(Node node);
}
