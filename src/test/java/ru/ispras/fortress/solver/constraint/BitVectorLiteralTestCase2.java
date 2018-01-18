/*
 * Copyright 2014-2018 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.solver.constraint;

import org.junit.Assert;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.data.types.datamap.DataMap;
import ru.ispras.fortress.solver.xml.XmlConstraintLoader;
import ru.ispras.fortress.solver.xml.XmlNotLoadedException;

import java.util.Arrays;

// TODO: The test is disabled. Need to investigate.
// It is not clear why it is needed and why it fails.
public class BitVectorLiteralTestCase2 { //extends GenericSolverTestBase {
  /*public BitVectorLiteralTestCase2() {
    super(new BitVectorLiteralConstraint2());
  }*/

  public static final class BitVectorLiteralConstraint2
      implements GenericSolverTestBase.SampleConstraint {

    @Override
    public Constraint getConstraint() {
      final String fileName = "./src/test/xml/mips_add_0.xml";
      try {
        return XmlConstraintLoader.loadFromFile(fileName);
      } catch (final XmlNotLoadedException e) {
        e.printStackTrace();
        Assert.fail(e.getMessage());
      }

      return null;
    }

    @Override
    public Iterable<Variable> getExpectedVariables() {
      final DataMap gpr1 = new DataMap(DataType.BIT_VECTOR(32), DataType.BIT_VECTOR(32));
      gpr1.put(
          Data.newBitVector("00000000000000000000000000000001", 2, 32),
          Data.newBitVector("00000000000000000000000000010000", 2, 32)
      );

      final DataMap gpr2 = new DataMap(DataType.BIT_VECTOR(32), DataType.BIT_VECTOR(32));
      gpr2.put(
          Data.newBitVector("00000000000000000000000000000000", 2, 32),
          Data.newBitVector("00000000000000000000000000000000", 2, 32)
      );
      gpr2.put(
          Data.newBitVector("00000000000000000000000000000001", 2, 32),
          Data.newBitVector("00000000000000000000000000010000", 2, 32)
      );

      final DataMap gpr4 = new DataMap(DataType.BIT_VECTOR(32), DataType.BIT_VECTOR(32));
      gpr4.put(
          Data.newBitVector("00000000000000000000000000000000", 2, 32),
          Data.newBitVector("00000000000000000000000000000000", 2, 32)
      );
      gpr4.put(
          Data.newBitVector("00000000000000000000000000000001", 2, 32),
          Data.newBitVector("00000000000000000000000000010000", 2, 32)
      );

      return Arrays.asList(
          new Variable("BRANCH!1", Data.newBitVector(0, 1)),
          new Variable("BRANCH!2", Data.newBitVector(0, 1)),
          new Variable("CIA!1", Data.newBitVector("00011111111111111111111111111100", 2, 32)),
          new Variable("CIA!2", Data.newBitVector("00000000000000000000000000000000", 2, 32)),
          new Variable("CIA!3", Data.newBitVector("00100000000000000000000000000000", 2, 32)),
          new Variable("CIA!4", Data.newBitVector("00100000000000000000000000000000", 2, 32)),

          new Variable("GPR!1", Data.newArray(gpr1)),
          new Variable("GPR!2", Data.newArray(gpr2)),
          new Variable("GPR!4", Data.newArray(gpr4)),

          new Variable("JMPADDR!1", Data.newBitVector(0, 32)),
          new Variable("JMPADDR!2", Data.newBitVector(0, 32)),
          new Variable("__tmp_0!1", Data.newBitVector("00000000000000000000000000010000", 2, 32)),
          new Variable("__tmp_0!2", Data.newBitVector(0, 32)),
          new Variable("__tmp_0!3", Data.newBitVector(0, 32)),
          new Variable("__tmp_0!4", Data.newBitVector(0, 32)),
          new Variable("__tmp_0!5", Data.newBitVector(0, 32)),
          new Variable("__tmp_1!1", Data.newBitVector("00000000000000000000000000010000", 2, 32)),
          new Variable("__tmp_1!2", Data.newBitVector(0, 32)),
          new Variable("__tmp_2!1", Data.newBitVector(0, 32)),
          new Variable("__tmp_3!1", Data.newBitVector(0, 32)),
          new Variable("__tmp_4!1", Data.newBitVector(0, 32)),
          new Variable("is_delay_slot!2", Data.newBitVector(0, 1)),
          new Variable("jump_address!2", Data.newBitVector(0, 32)),

          new Variable("mips_add.block_1!1", Data.newBoolean(false)),
          new Variable("mips_add.block_4!1", Data.newBoolean(false)),
          new Variable("mips_add.block_5!1", Data.newBoolean(true)),

          new Variable("mips_add.command.normal!1", Data.newBoolean(true)),
          new Variable("mips_add.command.overflow!1", Data.newBoolean(false)),

          new Variable("mips_add.command.rd.i!1", Data.newBitVector("00000", 2, 5)),
          new Variable("mips_add.command.rs.i!1", Data.newBitVector("00001", 2, 5)),
          new Variable("mips_add.command.rt.i!1", Data.newBitVector("00000", 2, 5)),

          new Variable("temp!1", Data.newBitVector("000000000000000000000000000000000", 2, 33)),
          new Variable("temp!2", Data.newBitVector("000000000000000000000000000100000", 2, 33))
      );
    }
  }
}