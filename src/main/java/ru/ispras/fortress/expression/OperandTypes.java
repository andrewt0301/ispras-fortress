package ru.ispras.fortress.expression;

/**
 * Operation family identifiers related to their operand types.
 * <p>When an operation identifier belongs to such a family, it means that the related
 * operation can have only operands of the specified type.</p>
 * @author <a href="mailto:smolov@ispras.ru">Sergey Smolov</a>
 */
enum OperandTypes {

  /* Operands are of same type. */
  SAME,

  /* Operands are of same bit vector type. */
  SAME_BV,

  /* Operands are of same logic type. */
  SAME_LOGIC,

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
