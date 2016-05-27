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

package ru.ispras.fortress.data.types.bitvector;

import static ru.ispras.fortress.util.InvariantChecks.checkNotNull;

/**
 * The BitVectorUnmodifiable class is a wrapper around a BitVector object that forbids modification
 * of data stored in the bit vector.
 * 
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
final class BitVectorUnmodifiable extends BitVector {
  private final BitVector bitVector;

  public BitVectorUnmodifiable(final BitVector bitVector) {
    checkNotNull(bitVector);
    this.bitVector = bitVector;
  }

  @Override
  public int getBitSize() {
    return bitVector.getBitSize();
  }

  @Override
  public int getByteSize() {
    return bitVector.getByteSize();
  }

  @Override
  public byte getByte(final int index) {
    return bitVector.getByte(index);
  }

  @Override
  public void setByte(final int index, final byte value) {
    throw new UnsupportedOperationException();
  }
}
