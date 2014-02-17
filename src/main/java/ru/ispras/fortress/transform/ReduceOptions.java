/*
 * Copyright (c) 2013 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * ReduceOptions.java, Nov 7, 2013 11:00:08 AM Andrei Tatarnikov
 */

package ru.ispras.fortress.transform;

/**
 * Describes flags that affect the behavior of the expression reduction logic.  
 * 
 * @author Andrei Tatarnikov
 */

public enum ReduceOptions
{
    /**
     * New instances of operations objects should be created for operations that were reduced.
     * Instances of other operation objects should be reduced. 
     */

    NEW_INSTANCE
}
