/*
 * Copyright (c) 2013 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * XMLNotSavedException.java, Dec 19, 2013 4:07:16 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver.xml;

public final class XMLNotSavedException extends Exception
{   
    private static final long serialVersionUID = 9002901081366259102L;

    private static final String MESSAGE = "Failed to save data to the '%s' document.";

    public XMLNotSavedException(String fileName, Throwable cause)
    {
        super(String.format(MESSAGE, fileName), cause);
    }

    @Override
    public String getMessage()
    {
        return String.format("%s Cause: %s", super.getMessage(), getCause().getMessage());
    }
}
