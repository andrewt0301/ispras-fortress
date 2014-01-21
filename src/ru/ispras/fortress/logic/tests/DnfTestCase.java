/*
 * Copyright 2014 Institute for System Programming of RAS (http://www.ispras.ru)
 *
 * Licensed under the Apache License, Version 2.0 (the "License")
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package ru.ispras.fortress.logic.tests;

import org.junit.*;

import ru.ispras.fortress.logic.*;

public class DnfTestCase
{
    @Test
    public void run()
    {
        NormalForm a = new NormalForm(NormalForm.Type.DNF);

        Clause x = new Clause();
        x.add(0, false);

        Clause y = new Clause();
        y.add(0, true);
        y.add(1, false);
        y.add(2, false);

        Clause z = new Clause();
        z.add(0, true);
        z.add(1, false);
        z.add(3, true);
        z.add(4, false);

        Clause u = new Clause();
        u.add(1, true);
        u.add(5, false);

        a.add(x);
        a.add(y);
        a.add(z);
        a.add(u);

        NormalForm b = DNF.orthogonalize(a);

        System.out.println(a);
        System.out.println(b);
    }
}