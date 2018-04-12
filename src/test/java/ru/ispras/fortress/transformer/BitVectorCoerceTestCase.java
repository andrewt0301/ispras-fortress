/*
 * Copyright 2018 ISP RAS (http://www.ispras.ru), UniTESK Lab (http://www.unitesk.com)
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

import org.junit.Assert;
import org.junit.Test;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;

/**
 * Test for "bit vector to bit vector" conversion methods.
 *
 * @author <a href="mailto:smolov@ispras.ru">Sergey Smolov</a>
 */
public class BitVectorCoerceTestCase {

  private static final Node BV_0_1 = NodeValue.newBitVector("0", 2, 1);
  private static final Node BV_1_1 = NodeValue.newBitVector("1", 2, 1);
  private static final Node BV_7_3 = NodeValue.newBitVector("111", 2, 3);

  private static final Node BV_1_VAR = NodeVariable.newBitVector("x", 1);
  private static final Node BV_3_VAR = NodeVariable.newBitVector("y", 3);

  private static final DataType BV_1_TYPE = DataType.bitVector(1);
  private static final DataType BV_3_TYPE = DataType.bitVector(3);

  @Test
  public void eqTypeValTest() {

    final Node sameTypeCoerced = TypeConversion.coerce(BV_1_1, BV_1_TYPE);
    Assert.assertEquals(BV_1_TYPE, sameTypeCoerced.getDataType());
  }

  @Test
  public void largeTypeValTest() {

    final Node largeTypeCoerced = TypeConversion.coerce(BV_0_1, BV_3_TYPE);
    Assert.assertEquals(BV_3_TYPE, largeTypeCoerced.getDataType());
  }

  @Test
  public void smallTypeValTest() {

    final Node smallTypeCoerced = TypeConversion.coerce(BV_7_3, BV_1_TYPE);
    Assert.assertEquals(smallTypeCoerced.getDataType(), BV_1_TYPE);
  }

  @Test
  public void eqTypeVarTest() {

    final Node eqTypeCoerced = TypeConversion.coerce(BV_1_VAR, BV_1_TYPE);
    Assert.assertEquals(eqTypeCoerced.getDataType(), BV_1_TYPE);
  }

  @Test
  public void largeTypeVarTest() {

    final Node largeTypeCoerced = TypeConversion.coerce(BV_1_VAR, BV_3_TYPE);
    Assert.assertEquals(largeTypeCoerced.getDataType(), BV_3_TYPE);
  }

  @Test
  public void smallTypeVarTest() {

    final Node smallTypeCoerced = TypeConversion.coerce(BV_3_VAR, BV_1_TYPE);
    Assert.assertEquals(smallTypeCoerced.getDataType(), BV_1_TYPE);
  }
}
