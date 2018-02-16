/*
 * Copyright 2016-2018 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.expression;

/**
 * Operation family identifiers related to their operand types.
 * <p>When an operation identifier belongs to such a family, it means that the related
 * operation can have only operands of the specified type.</p>
 *
 * @author <a href="mailto:smolov@ispras.ru">Sergey Smolov</a>
 */
enum OperandTypes {

  /* Operands are of same type. */
  SAME,

  /* Operands are of same bit vector type. */
  SAME_BV,

  /* Operands are of same logic numeric type (integer or real). */
  LOGIC_NUMERIC,

  /* Operands are of logic type. */
  LOGIC,

  /* Operands are of boolean type. */
  BOOL,

  /* Operands are of integer type. */
  INT,

  /* Operands are of bit vector type. */
  BV,

  /* If-then-else operands (special case). */
  ITE,

  /* First operand is an integer parameter, next one is a bit vector. */
  ONE_INT_PARAM_BV,

  /* First & second operands are of integer type, third one is a bit vector. */
  TWO_INT_PARAM_BV,

  /* Select operands (special case). */
  SELECT,

  /* Store operands (special case). */
  STORE,
}
