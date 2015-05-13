/*
 * Copyright 2007-2014 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.util;

/**
 * This class implements some methods for manipulating with bits.
 *
 * @author <a href="mailto:kamkin@ispras.ru">Alexander Kamkin</a>
 */
public final class BitUtils {
  private BitUtils() {}

  /**
   * Returns a bit mask of the given width.
   * 
   * @param width Mask width.
   * @return Integer bit mask.
   */
  public static int maskInt(final int width) {
    return width >= Integer.SIZE ? -1 : (1 << width) - 1;
  }

  /**
   * Returns a bit mask for the given range.
   * 
   * @param lo Lower bound.
   * @param hi Higher bound.
   * @return Integer bit mask.
   */
  public static int maskInt(final int lo, final int hi) {
    final int x = lo < hi ? lo : hi;
    int y = lo < hi ? hi : lo;

    if (y >= Integer.SIZE) {
      y = Integer.SIZE - 1;
    }

    return maskInt((y - x) + 1) << x;
  }

  /**
   * Returns a bit mask of the given width.
   * 
   * @param width Mask width.
   * @return Long bit mask.
   */
  public static long maskLong(final int width) {
    return width >= Long.SIZE ? -1 : (1 << width) - 1;
  }

  /**
   * Returns a bit mask for the given range.
   * 
   * @param lo Lower bound.
   * @param hi Higher bound.
   * @return Long bit mask.
   */
  public static long maskLong(final int lo, final int hi) {
    final int x = lo < hi ? lo : hi;
    int y = lo < hi ? hi : lo;

    if (y >= Long.SIZE) {
      y = Long.SIZE - 1;
    }

    return maskLong((y - x) + 1) << x;
  }
}
