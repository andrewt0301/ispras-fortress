/*
 * Copyright (c) 2011 ISPRAS (www.ispras.ru)
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * Environment.java, Dec 20, 2011 12:18:25 PM Andrei Tatarnikov
 * 
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not
 * use this file except in compliance with the License. You may obtain a copy of
 * the License at
 * 
 * http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations under
 * the License.
 */

package ru.ispras.fortress.solver;

/**
 * The Environment class provides methods to manage global the settings of the subsystem. 
 * 
 * @author Andrei Tatarnikov
 */

public final class Environment
{
    private Environment() {} 
    
    private static String solverPath;

	private static final String PRP_OS_NAME        = "os.name";
    private static final String PRP_CONSTRAINT_DIR = "ispras_solver_api: constraint-dir";

    static // Sets the default path to the external solver engine.
    {
        if (isUnix())
        {
            solverPath = "tools/z3/bin/z3";
        }
        else if(isWindows())
        {
            solverPath = "tools/z3/bin/z3.exe";
        }
        else if (Environment.isOSX())
        {
            solverPath = "tools/z3/bin/z3";
        }
        else
        {
            throw new IllegalStateException(String.format(
               "Unsupported platform: %s.", System.getProperty("os.name")));
        }
    }

    /**
     * Returns the path to the external constraint solver executable. 
     * @return Path
     */

    public static String getSolverPath()
    {
        return solverPath;
    }

    /**
     * Sets the path to the external constraint solver executable.
     * @param value Path
     */

    public static void setSolverPath(String value)
    {
        solverPath = value;
    }

    /**
     * Returns the path to the folder where constraints are stored.
     * @return Path
     */

    public static String getConstraintDir()
    {
        return System.getProperty(PRP_CONSTRAINT_DIR);
    }

    /**
     * Sets the path to the folder where constraints are stored.
     * @param value Path
     */

    public static void setConstraintDir(String value)
    {
        System.setProperty(PRP_CONSTRAINT_DIR, value);        
    }

    /**
     * Checks whether the tool is running in a Windows computer.
     * @return true if the tool is running in a Windows computer.
     */

    public static boolean isWindows()
    {
		final String os = System.getProperty(PRP_OS_NAME).toLowerCase();
		return os.contains("win");
	}
 
    /**
     * Checks whether the tool is running in a Unix or Linux computer.
     * @return true if the tool is running in a Unix or Linux computer.
     */

    public static boolean isUnix()
    {
        final String os = System.getProperty(PRP_OS_NAME).toLowerCase();
        return os.contains("nix") || os.contains("nux");
    }

    /**
     * Checks whether the tool is running in a Macintosh computer (under OS X).
     * @return true if the tool is running in a Macintosh computer (under OS X).
     */

    public static boolean isOSX()
    {
        final String os = System.getProperty(PRP_OS_NAME).toLowerCase();
        return os.contains("os x") || os.contains("mac");
    }
}
