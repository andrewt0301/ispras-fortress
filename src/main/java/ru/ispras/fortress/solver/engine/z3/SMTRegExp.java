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

package ru.ispras.fortress.solver.engine.z3;

public final class SMTRegExp {
  private SMTRegExp() {}

  public static final String SAT = "sat";
  public static final String UNSAT = "unsat";
  public static final String UNKNOWN = "unknown";

  public static final String TRUE = "true";
  public static final String FALSE = "false";

  public static final String VALUE_BIN = "[#][b][0|1]{1,}";
  public static final String VALUE_HEX = "[#][x][\\d|a-f|A-F]{1,}";
  public static final String VALUE_DEC = "\\(?(-\\s)?\\d+(\\.\\d+)?\\)?";

  public static final String VALUE_TRIM_PTRN = "^([#][b|x]){0,1}";
  public static final String LINE_START = "^";
}
