/*
 * Copyright 2018 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.expression.printer;

import org.junit.Assert;
import org.junit.Test;

/**
 * Tests for {@link SmtKeyword} class.
 *
 * @author <a href="mailto:smolov@ispras.ru">Sergey Smolov</a>
 */
public class SmtKeywordTestCase {

  @Test
  public void runTest() {

    final String negativeTestWord = "abc";
    Assert.assertFalse(SmtKeyword.isKeyword(negativeTestWord));

    final String positiveTestWord = "select";
    Assert.assertTrue(SmtKeyword.isKeyword(positiveTestWord));
  }
}
