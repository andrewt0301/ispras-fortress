/*
 * Copyright 2013-2018 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.solver.xml;

public class XmlNotLoadedException extends Exception {
  private static final long serialVersionUID = 4850967822331699405L;

  private static final String MESSAGE_FILE = "Failed to load data from the '%s' XML document.";
  private static final String MESSAGE_TEXT = "Failed to load data from XML text.";

  public XmlNotLoadedException(final String fileName, final Throwable cause) {
    super(String.format(MESSAGE_FILE, fileName), cause);
  }

  public XmlNotLoadedException(final Throwable cause) {
    super(MESSAGE_TEXT, cause);
  }

  @Override
  public String getMessage() {
    return String.format("%s Cause: %s", super.getMessage(), getCause().getMessage());
  }
}
