/*
 * Copyright 2016 ISP RAS (http://www.ispras.ru), UniTESK Lab (http://www.unitesk.com)
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package ru.ispras.fortress.transformer;

import org.junit.Assert;
import org.junit.Test;
import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.types.bitvector.BitVector;
import ru.ispras.fortress.data.types.datamap.DataMap;
import ru.ispras.fortress.expression.NodeValue;

/**
 * Test for map-to-bit vector converting method.
 * @author <a href="mailto:smolov@ispras.ru">Sergey Smolov</a>
 */
public class MapToBitVectorCoerceTestCase {

  @Test
  public void runTest() {

    final DataMap zeroStartMap = new DataMap(DataType.INTEGER, DataType.INTEGER);
    zeroStartMap.put(Data.newInteger(0), Data.newInteger(0));
    zeroStartMap.put(Data.newInteger(1), Data.newInteger(1));
    zeroStartMap.put(Data.newInteger(2), Data.newInteger(0));
    zeroStartMap.put(Data.newInteger(3), Data.newInteger(1));

    final NodeValue zeroStartBitVector = NodeValue.newBitVector(BitVector.valueOf("1010"));

    Assert.assertEquals(
        zeroStartBitVector,
        TypeConversion.coerce(newArray(zeroStartMap), DataType.BIT_VECTOR(4)));

    final DataMap oneStartMap = new DataMap(DataType.INTEGER, DataType.BIT_VECTOR(2));
    oneStartMap.put(Data.newInteger(1), Data.newBitVector(BitVector.valueOf("00")));
    oneStartMap.put(Data.newInteger(2), Data.newBitVector(BitVector.valueOf("01")));
    oneStartMap.put(Data.newInteger(3), Data.newBitVector(BitVector.valueOf("10")));
    oneStartMap.put(Data.newInteger(4), Data.newBitVector(BitVector.valueOf("11")));

    final NodeValue oneStartBitVector = NodeValue.newBitVector(BitVector.valueOf("11100100"));

    Assert.assertEquals(
        oneStartBitVector,
        TypeConversion.coerce(newArray(oneStartMap), DataType.BIT_VECTOR(8)));
  }

  private static NodeValue newArray(final DataMap map) {
    return new NodeValue(Data.newArray(map));
  }
}
