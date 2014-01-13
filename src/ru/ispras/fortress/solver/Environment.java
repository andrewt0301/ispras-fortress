/*
 * Copyright (c) 2011 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * Environment.java, Dec 20, 2011 12:18:25 PM Andrei Tatarnikov
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
    
	private static final String PRP_OS_NAME        = "os.name";
    private static final String PRP_SOLVER_PATH    = "ispras_solver_api: solver-path";
    private static final String PRP_CONSTRAINT_DIR = "ispras_solver_api: constraint-dir";

    /**
     * Returns the path to the external constraint solver executable. 
     * @return Path
     */

    public static String getSolverPath()
    {
        return System.getProperty(PRP_SOLVER_PATH);
    }

    /**
     * Sets the path to the external constraint solver executable.
     * @param value Path
     */

    public static void setSolverPath(String value)
    {
        System.setProperty(PRP_SOLVER_PATH, value);
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
