/*
 * Copyright 2014-2015 ISP RAS (http://www.ispras.ru)
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

package ru.ispras.fortress.data;

import static ru.ispras.fortress.util.InvariantChecks.checkNotNull; 

import java.util.EnumMap;
import java.util.Map;

import ru.ispras.fortress.data.types.bitvector.BitVector;
import ru.ispras.fortress.randomizer.Randomizer;

/**
 * The Random class provides facilities to generate random data ({@link Data} and {@link Variable}
 * objects). The current implementation uses the {@link Randomizer} class to generate random values.
 * It is possible to customize the behavior by providing a custom generation engine (a custom
 * implementation of the {@link Random.Engine} interface).
 * 
 * @author Andrei Tatarnikov
 */

public final class Random {
  private Random() {}

  /**
   * The Engine interface is a common interface to be implemented by all generation engines. It
   * provides methods for generating data and setting up the randomizer.
   * 
   * @author Andrei Tatarnikov
   */

  public interface Engine {
    /**
     * Sets up the generation engine (if it requires some setup before being used).
     */

    void setUp();

    /**
     * Sets a new seed of the random data generation engine.
     * 
     * @param seed The seed to be set.
     */

    void setSeed(int seed);

    /**
     * Generated random data of the specified type and size.
     * 
     * @param typeId Data type identifier.
     * @param size Data type size (in bits).
     * @return A random data.
     * 
     * @throws UnsupportedOperationException if random data generation is not supported by the given
     *         data type.
     */

    Data random(DataTypeId typeId, int size);
  }

  /**
   * The TypedGenerator interface is a common interface for objects that are responsible for
   * generating data of some specific type.
   * 
   * @author Andrei Tatarnikov
   */

  public interface TypedGenerator {
    /**
     * Generates random data. Data type depends on the implementation.
     * 
     * @param size Data size.
     * @return Random data.
     */

    Data generate(int size);
  }

  /**
   * The Initializer interface is to be implemented by objects that are responsible for initializing
   * some specific generation engine.
   * 
   * @author Andrei Tatarnikov
   */

  public interface Initializer {
    /**
     * Sets up the generation engine (if it requires some setup before being used).
     */

    void setUp();

    /**
     * Sets a new seed of the random data generation engine.
     * 
     * @param seed The seed to be set.
     */

    void setSeed(int seed);
  }

  /**
   * The CompositeEngine class is a reusable implementation of the Engine interface. It uses a set
   * of objects that provide facilities to set up the randomizer and to generate data of specific
   * types.
   * 
   * @author Andrei Tatarnikov
   */

  public static final class CompositeEngine implements Engine {
    private static final String ERR_UNSUPPORTED =
        "Random data generation is not supported for the %s type.";

    private final Initializer initializer;
    private final Map<DataTypeId, TypedGenerator> generators;

    /**
     * Constructs a CompositeEngine object that uses the specified initializer.
     * 
     * @param initializer Initializer to be used to set up the randomizer.
     */

    public CompositeEngine(final Initializer initializer) {
      checkNotNull(initializer);
      this.initializer = initializer;
      this.generators = new EnumMap<DataTypeId, TypedGenerator>(DataTypeId.class);
    }

    /**
     * Sets a generator responsible for generating data of the specified type.
     * 
     * @param typeId Type identifier.
     * @param generator Generator to the specified type.
     * 
     * @throws NullPointerException if any of the parameters equals null.
     */

    public void setGenerator(final DataTypeId typeId, final TypedGenerator generator) {
      checkNotNull(typeId);
      checkNotNull(generator);
      generators.put(typeId, generator);
    }

    /** {@inheritDoc} */

    @Override
    public void setUp() {
      initializer.setUp();
    }

    /** {@inheritDoc} */

    @Override
    public void setSeed(final int seed) {
      initializer.setSeed(seed);
    }

    /**
     * {@inheritDoc}
     * 
     * @throws NullPointerException if the typeId parameter equals null.
     * @throws UnsupportedOperationException if random data generation is not supported by the given
     *         data type.
     */

    @Override
    public Data random(final DataTypeId typeId, final int size) {
      checkNotNull(typeId);

      if (!generators.containsKey(typeId)) {
        throw new UnsupportedOperationException(String.format(ERR_UNSUPPORTED, typeId));
      }

      final TypedGenerator generator = generators.get(typeId);
      return generator.generate(size);
    }
  }

  /**
   * Random data generation engine used to generate data (singleton).
   */

  private static Engine engine = null;

  /**
   * Creates the default random data generation engine based on the CompositeEngine class.
   * 
   * @return An instance of the default random data generation engine.
   */

  private static Engine createDefaultEngine() {
    final CompositeEngine result = new CompositeEngine(new Initializer() {
      @Override
      public void setSeed(final int seed) {
        Randomizer.get().setSeed(seed);
      }

      @Override
      public void setUp() { /* Nothing */}
    });

    result.setGenerator(DataTypeId.LOGIC_BOOLEAN, new TypedGenerator() {
      @Override
      public Data generate(final int size) {
        return Data.newBoolean(Randomizer.get().next() % 2 == 0);
      }
    });

    result.setGenerator(DataTypeId.LOGIC_INTEGER, new TypedGenerator() {
      @Override
      public Data generate(final int size) {
        return Data.newInteger(Randomizer.get().nextInt());
      }
    });

    result.setGenerator(DataTypeId.BIT_VECTOR, new TypedGenerator() {
      @Override
      public Data generate(final int size) {
        final BitVector data = BitVector.newEmpty(size);
        Randomizer.get().fill(data);
        return Data.newBitVector(data);
      }
    });

    return result;
  }

  /**
   * Returns an instance of the random data generation engine. If the method is called for the first
   * time and no custom engine has been set up by setEngine method, a default engine is created and
   * returned.
   * 
   * @return Random data generation engine being used.
   */

  public static Engine getEngine() {
    if (null == engine) {
      engine = createDefaultEngine();
    }

    return engine;
  }

  /**
   * Sets the random data generation engine to be used to generate data.
   * 
   * @param value Random data generation engine.
   * 
   * @throws NullPointerException if the parameter equals null.
   */

  public static void setEngine(final Engine value) {
    checkNotNull(value);
    engine = value;
  }

  /**
   * Sets a new seed of the random data generation engine.
   * 
   * @param seed The seed to be set.
   */

  public static void setSeed(final int seed) {
    getEngine().setSeed(seed);
  }

  /**
   * Creates a data object of the specified type initialized with a random value.
   * 
   * @param type Data type.
   * @return Random data.
   * 
   * @throws NullPointerException if the parameter equals null.
   * @throws UnsupportedOperationException if random data generation is not supported by the given
   *         data type.
   */

  public static Data newValue(final DataType type) {
    checkNotNull(type);
    return getEngine().random(type.getTypeId(), type.getSize());
  }

  /**
   * Creates a variable of the specified type initialized with a random value.
   * 
   * @param name Variable name.
   * @param type Variable data type.
   * @return Variable initialized with a random value.
   * 
   * @throws NullPointerException if any of the parameters equals null.
   * @throws UnsupportedOperationException if random data generation is not supported by the given
   *         data type.
   */

  public static Variable newVariable(final String name, final DataType type) {
    checkNotNull(name);
    checkNotNull(type);
    return new Variable(name, newValue(type));
  }

  /**
   * Assigns a random value to the specified variable.
   * 
   * @param variable Variable to be assigned.
   * @return Variable with a value assigned (same instance).
   * 
   * @throws NullPointerException if the parameter equals null.
   * @throws UnsupportedOperationException if random data generation is not supported by the given
   *         data type.
   */

  public static Variable assignValue(final Variable variable) {
    checkNotNull(variable);
    variable.setData(newValue(variable.getType()));
    return variable;
  }
}
