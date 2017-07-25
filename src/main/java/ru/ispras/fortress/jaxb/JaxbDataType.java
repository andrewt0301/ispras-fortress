/*
 * Copyright 2014 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.jaxb;

import ru.ispras.fortress.data.DataType;

/**
 * The representation of {@link DataType} suitable for JAXB marshalling and unmarshalling. This
 * class must be used only for JAXB operations.
 * 
 * @see DataType
 */
public enum JaxbDataType {
  BIT_VECTOR,
  LOGIC_BOOLEAN,
  LOGIC_INTEGER,
  LOGIC_REAL,
  UNKNOWN
}
