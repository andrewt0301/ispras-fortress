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

package ru.ispras.fortress.logic;

import org.junit.*;

public class DnfTestCase {
  protected NormalForm createDnf() {
    NormalForm a = new NormalForm(NormalForm.Type.DNF);

    Clause x0 = new Clause();

    for (int i = 0; i < 10; i++) {
      x0.add(i + 100, false);
    }

    Clause x = new Clause();
    x.add(0, false);

    Clause x1 = new Clause();
    x1.add(0, false);

    Clause y = new Clause();
    y.add(0, true);
    y.add(1, false);
    y.add(2, false);
    y.add(3, false);

    Clause z = new Clause();
    z.add(0, true);
    z.add(1, false);
    z.add(4, true);
    z.add(5, false);

    Clause u = new Clause();
    u.add(1, false);
    u.add(6, false);

    a.add(x0);
    a.add(x);
    a.add(x1);
    a.add(y);
    a.add(z);
    a.add(u);

    for (int i = 0; i < 10; i++) {
      a.add(y);
    }

    for (int i = 0; i < 10; i += 4) {
      u.add(i, (i & 1) == 0);
      a.add(u);
    }

    for (int i = 0; i < 10; i++) {
      z.add(i, (i & 1) == 0);
      z.add(i + 1000, (i & 1) == 0);
      a.add(z);
    }

    return a;
  }

  @Test
  public void run() {
    NormalForm x = createDnf();
    NormalForm y = Orthogonalizer.orthogonalize(x);

    System.out.println(x);
    System.out.println(y);
  }
}
