/*
 * Copyright (c) 2013 ISPRAS
 * 
 * Institute for System Programming of Russian Academy of Sciences
 * 
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 * 
 * All rights reserved.
 * 
 * SMTConst.java, Dec 18, 2013 11:47:40 AM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver.engine.z3;

import java.util.EnumMap;
import java.util.Map;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.DataTypeId;
import ru.ispras.fortress.data.types.bitvector.BitVector;

public final class SMTStrings
{
    private SMTStrings() {}
    
    public static String sSPACE          = " ";
    public static String sBRACKET_OPEN   = "(";
    public static String sBRACKET_CLOSE  = ")";
    public static String sHYPHEN         = "-";
    public static String sUNDERLINE      = "_";

    public static String sZERO           = "0";
    public static String sONE            = "1";

    public static String sEMPTY          = ""; 
    public static String sTRUE           = "true";
    public static String sFALSE          = "false";
    public static String sDEFAULT_ARRAY  = "DefaultArrayLiteral!%d";

    public static String sBV_BIN_PREFIX  = "#b";
    public static String sBV_HEX_PREFIX  = "#x";

    public static String sTYPE_BOOL      = "Bool";
    public static String sTYPE_INT       = "Int";
    public static String sTYPE_REAL      = "Real";
    public static String sTYPE_BITVECTOR = "(_ BitVec %d)";
    public static String sTYPE_ARRAY     = "(Array %s %s)";

    public static String sASSERT         = "(assert %s)%n";
    public static String sDECLARE_CONST  = "(declare-const %s %s)%n";
    public static String sDEFINE_FUN     = "(define-fun %s)%n";
    public static String sCHECK_SAT      = "(check-sat)";
    public static String sGET_VALUE      = "(get-value (%s))%n";
    public static String sGET_MODEL      = "(get-model)";
    public static String sEXIT           = "(exit)";

    public static String sNEGATION       = "(- %s)";
    public static String sPARAM_DEF      = "(%s %s)"; 

    private static final Map<DataTypeId, String> typeMap = createTypeMap();
    private static Map<DataTypeId, String> createTypeMap()
    {
        final Map<DataTypeId, String> result = 
            new EnumMap<DataTypeId, String>(DataTypeId.class);

        result.put(DataTypeId.BIT_VECTOR,    sTYPE_BITVECTOR);
        result.put(DataTypeId.LOGIC_BOOLEAN, sTYPE_BOOL);
        result.put(DataTypeId.LOGIC_INTEGER, sTYPE_INT);
        result.put(DataTypeId.LOGIC_REAL,    sTYPE_REAL);
        result.put(DataTypeId.MAP,           sTYPE_ARRAY);

        return result;
    }

    public static String textForType(DataType type)
    {
        if (null == type)
            throw new NullPointerException();

        if (!typeMap.containsKey(type.getTypeId()))
            throw new IllegalArgumentException("Unsupported type: " + type.getTypeId());

        final Object[] parameters = type.getParameters();
        for (int i = 0; i < parameters.length; ++i)
            if (parameters[i] instanceof DataType)
                parameters[i] = textForType((DataType) parameters[i]);

        return String.format(typeMap.get(type.getTypeId()), parameters);
    }
    
    public static String textForData(Data data)
    {
        if (null == data)
            throw new NullPointerException();
        
        switch(data.getType().getTypeId())
        {
            case BIT_VECTOR:
            {
                final BitVector value = (BitVector) data.getValue();
                return (data.getType().getTypeRadix() == 16) ?
                    sBV_HEX_PREFIX + value.toHexString() : sBV_BIN_PREFIX + value.toBinString();
            }

            case LOGIC_BOOLEAN:
            {
                final Boolean value = (Boolean) data.getValue();
                return value ? sTRUE : sFALSE;
            }

            case LOGIC_INTEGER:
            {
                final int value = (Integer) data.getValue();
                return (value >= 0) ? Integer.toString(value) : String.format(sNEGATION, Math.abs(value));
            }

            case LOGIC_REAL:
            {
                final double value = (Double) data.getValue();
                return (value >= 0) ? Double.toString(value) : String.format(sNEGATION, Math.abs(value));
            }

            case MAP:
            {
                final Map<Data, Data> map = (Map<Data, Data>) data.getValue();
                final StringBuilder builder = new StringBuilder();

                final String prefix = "(store ";

                builder.ensureCapacity(prefix.length() * map.size() + sDEFAULT_ARRAY.length());
                for (int i = 0; i < map.size(); ++i)
                    builder.append(prefix);
                builder.append(sDEFAULT_ARRAY).append(sSPACE);

                for (Map.Entry<Data, Data> entry : map.entrySet())
                    builder .append(textForData(entry.getKey()))
                            .append(" ")
                            .append(textForData(entry.getValue()))
                            .append(") ");
                return builder.toString();
            }

            default: // Unknown value type
            {
                throw new IllegalArgumentException("Unsupported data type: " + data.getType().getTypeId());
            }
        }
    }
}
