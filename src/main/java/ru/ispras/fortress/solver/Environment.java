/*
 * Copyright 2011-2014 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.solver;

/**
 * The Environment class provides methods to manage global the settings of the subsystem.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public final class Environment {
  private Environment() {}

  private static boolean isDebugMode = false;
  private static final String PRP_OS_NAME = "os.name";

  /**
   * Gets the name of the operating system the tool is running under.
   *
   * @return Operating system name.
   */
  public static String getOsName() {
    return System.getProperty(PRP_OS_NAME);
  }

  /**
   * Checks whether the tool is running in a Windows computer.
   *
   * @return true if the tool is running in a Windows computer.
   */
  public static boolean isWindows() {
    final String os = getOsName().toLowerCase();
    return os.contains("win");
  }

  /**
   * Checks whether the tool is running in a Unix or Linux computer.
   *
   * @return true if the tool is running in a Unix or Linux computer.
   */
  public static boolean isUnix() {
    final String os = getOsName().toLowerCase();
    return os.contains("nix") || os.contains("nux");
  }

  /**
   * Checks whether the tool is running in a Macintosh computer (under OS X).
   *
   * @return true if the tool is running in a Macintosh computer (under OS X).
   */
  public static boolean isOsX() {
    final String os = getOsName().toLowerCase();
    return os.contains("os x") || os.contains("mac");
  }

  /**
   * Checks whether debug mode is enabled.
   *
   * @return {@code true} if debug mode is enabled or {@code false} otherwise.
   */
  public static boolean isDebugMode() {
    return isDebugMode;
  }

  /**
   * Enables or disables debug mode.
   *
   * @param isDebugMode Status of debug mode to be set ({@code true} or {@code false}).
   */
  public static void setDebugMode(final boolean isDebugMode) {
    Environment.isDebugMode = isDebugMode;
  }
}
