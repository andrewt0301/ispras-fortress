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

import java.math.BigInteger;
import java.util.EnumMap;
import java.util.Map;

import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.DataTypeId;
import ru.ispras.fortress.data.types.bitvector.BitVector;

public final class SMTStrings
{
    private SMTStrings() {}
    
    public static final String sSPACE          = " ";
    public static final String sBRACKET_OPEN   = "(";
    public static final String sBRACKET_CLOSE  = ")";
    public static final String sHYPHEN         = "-";
    public static final String sUNDERLINE      = "_";

    public static final String sZERO           = "0";
    public static final String sONE            = "1";

    public static final String sEMPTY          = ""; 
    public static final String sTRUE           = "true";
    public static final String sFALSE          = "false";
    public static final String sDEFAULT_ARRAY  = "DefaultArrayLiteral!%d";

    public static final String sBV_BIN_PREFIX  = "#b";
    public static final String sBV_HEX_PREFIX  = "#x";

    public static final String sTYPE_BOOL      = "Bool";
    public static final String sTYPE_INT       = "Int";
    public static final String sTYPE_REAL      = "Real";
    public static final String sTYPE_BITVECTOR = "(_ BitVec %d)";
    public static final String sTYPE_ARRAY     = "(Array %s %s)";

    public static final String sASSERT         = "(assert %s)%n";
    public static final String sDECLARE_CONST  = "(declare-const %s %s)%n";
    public static final String sDEFINE_FUN     = "(define-fun %s)%n";
    public static final String sCHECK_SAT      = "(check-sat)";
    public static final String sGET_VALUE      = "(get-value (%s))%n";
    public static final String sGET_MODEL      = "(get-model)";
    public static final String sEXIT           = "(exit)";

    public static final String sNEGATION       = "(- %s)";
    public static final String sPARAM_DEF      = "(%s %s)"; 

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
                final BigInteger value = (BigInteger) data.getValue();
                return (value.compareTo(BigInteger.ZERO) >= 0) ? value.toString() : String.format(sNEGATION, value.abs());
            }

            case LOGIC_REAL:
            {
                final double value = (Double) data.getValue();
                return (value >= 0) ? Double.toString(value) : String.format(sNEGATION, Math.abs(value));
            }

            case MAP:
            {
                // Map<Data, Data> is assumed.
                final Map<?, ?> map = (Map<?, ?>) data.getValue();
                final StringBuilder builder = new StringBuilder();

                final String prefix = "(store ";

                builder.ensureCapacity(prefix.length() * map.size() + sDEFAULT_ARRAY.length());
                for (int i = 0; i < map.size(); ++i)
                    builder.append(prefix);
                builder.append(sDEFAULT_ARRAY).append(sSPACE);

                for (Map.Entry<?, ?> entry : map.entrySet())
                {
                    builder .append(textForData((Data) entry.getKey()))
                            .append(" ")
                            .append(textForData((Data) entry.getValue()))
                            .append(") ");
                }
                return builder.toString();
            }

            default: // Unknown value type
            {
                throw new IllegalArgumentException("Unsupported data type: " + data.getType().getTypeId());
            }
        }
    }
}
