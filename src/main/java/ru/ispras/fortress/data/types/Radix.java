/*
 * Copyright 2013-2014 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.data.types;

/**
 * The Radix enumeration describes radixes to be used to convert a value to a string or vice versa.
 * 
 * @author Andrei Tatarnikov
 */

public enum Radix {
  /** Radix for binary data. */
  BIN(2),

  /** Radix for decimal data. */
  DEC(10),

  /** Radix for hexadecimal data. */
  HEX(16);

  private final int value;

  private Radix(final int value) {
    this.value = value;
  }

  public int value() {
    return value;
  }
}
