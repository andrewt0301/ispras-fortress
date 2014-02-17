/*
 * Copyright (c) 2013 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * XMLNotLoadedException.java, Dec 19, 2013 4:57:12 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver.xml;

public class XMLNotLoadedException extends Exception
{
    private static final long serialVersionUID = 4850967822331699405L;

    private static final String MESSAGE = "Failed to load data from '%s' document.";

    public XMLNotLoadedException(String fileName, Throwable cause)
    {
        super(String.format(MESSAGE, fileName), cause);
    }
    
    @Override
    public String getMessage()
    {
        return String.format("%s Cause: %s", super.getMessage(), getCause().getMessage());
    }
}
