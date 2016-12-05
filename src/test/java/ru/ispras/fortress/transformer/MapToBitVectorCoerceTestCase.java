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

  private static final Data INT_0 = Data.newInteger(0);
  private static final Data INT_1 = Data.newInteger(1);
  private static final Data INT_2 = Data.newInteger(2);
  private static final Data INT_3 = Data.newInteger(3);
  private static final Data INT_4 = Data.newInteger(4);

  private static final Data BV2_0 = Data.newBitVector(BitVector.valueOf("00"));
  private static final Data BV2_1 = Data.newBitVector(BitVector.valueOf("01"));
  private static final Data BV2_2 = Data.newBitVector(BitVector.valueOf("10"));
  private static final Data BV2_3 = Data.newBitVector(BitVector.valueOf("11"));

  private static final NodeValue ONE_START_BV =
      NodeValue.newBitVector(BitVector.valueOf("11100100"));

  @Test
  public void zeroStartMapTest() {

    /* Convert int-to-int map (starting from 0 index) to bit vector. */
    final DataMap zeroStartMap = new DataMap(DataType.INTEGER, DataType.INTEGER);
    zeroStartMap.put(INT_0, INT_0);
    zeroStartMap.put(INT_1, INT_1);
    zeroStartMap.put(INT_2, INT_0);
    zeroStartMap.put(INT_3, INT_1);

    final NodeValue zeroStartBitVector = NodeValue.newBitVector(BitVector.valueOf("1010"));

    Assert.assertEquals(
        zeroStartBitVector,
        TypeConversion.coerce(newArray(zeroStartMap), DataType.BIT_VECTOR(4)));
  }

  @Test
  public void oneStartMapTest() {
    /* Convert int-to-"bit vector" map (starting from 1 index) to bit vector. */
    final DataMap oneStartMap = new DataMap(DataType.INTEGER, DataType.BIT_VECTOR(2));
    oneStartMap.put(INT_1, BV2_0);
    oneStartMap.put(INT_2, BV2_1);
    oneStartMap.put(INT_3, BV2_2);
    oneStartMap.put(INT_4, BV2_3);

    Assert.assertEquals(
        ONE_START_BV,
        TypeConversion.coerce(newArray(oneStartMap), DataType.BIT_VECTOR(8)));
  }

  @Test
  public void bvToBvMapTest() {

    /* Convert "bit vector"-to-"bit vector" map to bit vector. */
    final DataMap bvToBvMap = new DataMap(DataType.BIT_VECTOR(2), DataType.BIT_VECTOR(2));
    bvToBvMap.put(BV2_0, BV2_0);
    bvToBvMap.put(BV2_1, BV2_1);
    bvToBvMap.put(BV2_2, BV2_2);
    bvToBvMap.put(BV2_3, BV2_3);

    Assert.assertEquals(
        ONE_START_BV,
        TypeConversion.coerce(newArray(bvToBvMap), DataType.BIT_VECTOR(8)));
  }

  @Test
  public void boolToIntMapTest() {

    /* Convert boolean-to-int map to bit vector. */
    final DataMap boolToIntMap = new DataMap(DataType.BOOLEAN, DataType.INTEGER);
    boolToIntMap.put(Data.newBoolean(false), INT_1);
    boolToIntMap.put(Data.newBoolean(true), INT_0);

    final NodeValue booleanVector = NodeValue.newBitVector(BitVector.valueOf("01"));
    Assert.assertEquals(
        booleanVector,
        TypeConversion.coerce(newArray(boolToIntMap), DataType.BIT_VECTOR(2)));
  }

  private static NodeValue newArray(final DataMap map) {
    return new NodeValue(Data.newArray(map));
  }
}
