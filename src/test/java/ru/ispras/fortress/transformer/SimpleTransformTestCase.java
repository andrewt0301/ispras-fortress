package ru.ispras.fortress.transformer;

import org.junit.*;

import java.util.List;
import java.util.Collections;

import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.data.DataType;

import ru.ispras.fortress.expression.*;

public class SimpleTransformTestCase
{
    private static NodeVariable createVariable(String name)
    {
        final Variable var = new Variable(name, DataType.INTEGER);
        return new NodeVariable(var);
    }

    private static NodeExpr PLUS(Node ... args)
    {
        return new NodeExpr(StandardOperation.PLUS, args);
    }

    private static NodeExpr EQ(Node lhs, Node rhs)
    {
        return new NodeExpr(StandardOperation.EQ, lhs, rhs);
    }

    private static NodeBinding singleBinding(NodeVariable variable, Node value, Node expr)
    {
        final List<NodeBinding.BoundVariable> bindings =
            Collections.singletonList(NodeBinding.bindVariable(variable, value));

        return new NodeBinding(expr, bindings);
    }

    @Test
    public void substituteSingleVariable()
    {
        final Node a = createVariable("a");
        final Node b = createVariable("b");
        final Node c = createVariable("c");

        // (a = b + c)
        final Node expr = EQ(a, PLUS(b, c));
        final Node firstExpected = EQ(a, PLUS(a, c));
        final Node firstPass = Transformer.substitute(expr, "b", a);
        Assert.assertTrue(firstExpected.toString().equals(firstPass.toString()));

        final Node secondExpected = EQ(c, PLUS(c, c));
        final Node secondPass = Transformer.substitute(firstPass, "a", c);
        Assert.assertTrue(secondExpected.toString().equals(secondPass.toString()));
    }

    @Test
    public void substituteWithinBinding()
    {
        final NodeVariable a = createVariable("a");
        final NodeVariable x = createVariable("x");
        final NodeVariable y = createVariable("y");

        final Node let = singleBinding(a, PLUS(x, y), PLUS(x, a));
        final Node unchanged = Transformer.substitute(let, "a", x);

        Assert.assertTrue(unchanged.toString().equals(let.toString()));

        final Node changed = Transformer.substitute(let, "x", y);
        final Node expected = singleBinding(a, PLUS(y, y), PLUS(y, a));

        Assert.assertTrue(changed.toString().equals(expected.toString()));
    }
}