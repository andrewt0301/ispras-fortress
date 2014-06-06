package ru.ispras.fortress.data;

import org.junit.*;
import java.util.Map;

public class DataTypeTestCase
{
    @Test
    @SuppressWarnings("unchecked")
    public void parseKeyValue()
    {
        final String strval = "((1:2)(2:3)(3:4))";
        final DataType type = DataType.MAP(DataType.INTEGER, DataType.INTEGER);
        final Data data = type.valueOf(strval, 10);

        Assert.assertTrue(data.getValue() instanceof Map);

        final Map<Data, Data> map = (Map<Data, Data>) data.getValue();
        Assert.assertTrue(map.size() == 3);

        for (Map.Entry<Data, Data> entry : map.entrySet())
        {
            int key = (Integer) entry.getKey().getValue();
            int value = (Integer) entry.getValue().getValue();
            Assert.assertTrue(value == key + 1);
        }
    }
}
