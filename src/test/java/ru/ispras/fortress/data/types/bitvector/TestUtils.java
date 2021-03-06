/*
 * Copyright 2012-2018 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.data.types.bitvector;

import org.junit.Assert;

public final class TestUtils {
  private TestUtils() {}

  private static final boolean OUTPUT_DEBUG_STRINGS = true;

  private static final String SEPARATOR = "/"
      + "******************************************************************" + "%n* %-64s*%n"
      + "*******************************************************************" + "/";

  public static void trace(final String text) {
    if (OUTPUT_DEBUG_STRINGS) {
      System.out.println(text);
    }
  }

  public static void header(final String title) {
    trace(String.format(SEPARATOR, title));
  }

  public static void checkBitVector(BitVector current, BitVector expected) {
    checkBitVector(current, expected.toBinString());
  }

  public static void checkBitVector(BitVector current, String expected) {
    final String dataString = current.toBinString();
    trace(String.format("Data:     %32s%nExpected: %32s", dataString, expected));

    Assert.assertTrue(
        String.format("Values do not match. %s (data) != %s (expected)", dataString, expected),
        expected.equals(dataString));
  }

  public static void checkBitVector(BitVector current, int expected) {
    checkBitVector(current, toBinString(expected, current.getBitSize()));
  }

  public static void checkBitVector(BitVector data, long expected) {
    checkBitVector(data, TestUtils.toBinString(expected, data.getBitSize()));
  }

  public static String toBinString(int value, int bitSize) {
    final String binstr = Integer.toBinaryString(value);

    if (binstr.length() > bitSize) {
      return binstr.substring(binstr.length() - bitSize, binstr.length());
    }

    final int count = bitSize - binstr.length();
    return (count > 0) ? String.format("%0" + count + "d", 0) + binstr : binstr;
  }

  public static String toBinString(long value, int bitSize) {
    final String binstr = Long.toBinaryString(value);

    if (binstr.length() > bitSize) {
      return binstr.substring(binstr.length() - bitSize, binstr.length());
    }

    final int count = bitSize - binstr.length();
    return (count > 0) ? String.format("%0" + count + "d", 0) + binstr : binstr;
  }

  public static String comparisonMsg(int val) {
    switch (val) {
      case -1:
        return "<";
      case 0:
        return "==";
      case 1:
        return ">";
      default:
        ;
    }
    return "failed to compare with";
  }

  public static void checkComparison(BitVector lhs, BitVector rhs, int expected) {
    final String lstr = lhs.toBinString();
    final String rstr = rhs.toBinString();
    trace(String.format("Comparison lhs: %32s%nComparison rhs: %32s", lstr, rstr));

    int actual = lhs.compareTo(rhs);

    Assert.assertTrue(String.format("Wrong comparison result. %s (lhs) %s %s (rhs), expected %s",
        lstr, comparisonMsg(actual), rstr, comparisonMsg(expected)), actual == expected);
  }
}
