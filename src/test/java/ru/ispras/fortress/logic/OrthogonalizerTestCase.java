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

package ru.ispras.fortress.logic;

import org.junit.Test;

public final class OrthogonalizerTestCase {
  private NormalForm createDnf() {
    final NormalForm.Builder a = new NormalForm.Builder(NormalForm.Type.DNF);

    final Clause.Builder x0 = new Clause.Builder();

    for (int i = 0; i < 10; i++) {
      x0.add(i + 100, false);
    }

    final Clause.Builder x = new Clause.Builder();
    x.add(0, false);

    final Clause.Builder x1 = new Clause.Builder();
    x1.add(0, false);

    final Clause.Builder y = new Clause.Builder();
    y.add(0, true);
    y.add(1, false);
    y.add(2, false);
    y.add(3, false);

    final Clause.Builder z = new Clause.Builder();
    z.add(0, true);
    z.add(1, false);
    z.add(4, true);
    z.add(5, false);

    final Clause.Builder u = new Clause.Builder();
    u.add(1, false);
    u.add(6, false);

    a.add(x0.build());
    a.add(x.build());
    a.add(x1.build());
    a.add(y.build());
    a.add(z.build());
    a.add(u.build());

    for (int i = 0; i < 10; i++) {
      a.add(y.build());
    }

    for (int i = 0; i < 10; i += 4) {
      u.add(i, (i & 1) == 0);
      a.add(u.build());
    }

    for (int i = 0; i < 10; i++) {
      z.add(i, (i & 1) == 0);
      z.add(i + 1000, (i & 1) == 0);
      a.add(z.build());
    }

    return a.build();
  }

  @Test
  public void run() {
    final NormalForm x = createDnf();
    final NormalForm y = Orthogonalizer.orthogonalize(x);

    System.out.println(x);
    System.out.println(y);
  }
}
