package ru.ispras.fortress.transform;

import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeExpr;

public interface TransformRule
{
    public Node apply(NodeExpr expr);
}
