/*
 * Copyright (c) 2011 ISPRAS
 *
 * Institute for System Programming of Russian Academy of Sciences
 *
 * 25 Alexander Solzhenitsyn st. Moscow 109004 Russia
 *
 * All rights reserved.
 *
 * Z3TextSolver.java, Dec 20, 2011 12:18:52 PM Andrei Tatarnikov
 */

package ru.ispras.fortress.solver.engine.z3;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.EnumSet;
import java.util.Iterator;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.Map;
import java.util.HashMap;
import java.util.List;
import java.util.ArrayList;


import ru.ispras.fortress.data.Data;
import ru.ispras.fortress.data.DataType;
import ru.ispras.fortress.data.Variable;
import ru.ispras.fortress.expression.*;
import ru.ispras.fortress.solver.Environment;
import ru.ispras.fortress.solver.SolverBase;
import ru.ispras.fortress.solver.SolverResult;
import ru.ispras.fortress.solver.SolverResultBuilder;
import ru.ispras.fortress.solver.constraint.Constraint;
import ru.ispras.fortress.solver.constraint.ConstraintKind;
import ru.ispras.fortress.solver.constraint.Formulas;

/**
 * The Z3TextSolver class implements logic of a constraint solver that
 * uses the Z3 tool by Microsoft Research. The constraint is translated
 * to STM-LIB code that is then saved to a file and processed to the tool.
 *
 * @author Andrei Tatarnikov
 */

public final class Z3TextSolver extends SolverBase
{
    private static final String NAME =
        "Z3 (text-based interface)";

    private static final String DESCRIPTION =
        "Solves constraints using the Z3 solver. Interacts with thesolver via text files and command line.";

    private static final String TEMP_FILE           = "ispras_z3_temp";
    private static final String TEMP_FILE_SUFFIX    = ".smt2";

    private static final String UNK_OUTPUT_ERR_FRMT =
        "Unexpected solver output: \"%s\"";

    private static final String IO_EXCEPTION_ERR =
        "I/O exception in the process of a solving the constraint. Details: ";
    
    private static final String UNSUPPORTED_KIND_ERR =
        "Unsupported constraint type: %s.%s.";

    public Z3TextSolver()
    {
        super(
            NAME,
            DESCRIPTION,
            EnumSet.of(ConstraintKind.FORMULA_BASED),
            true
        );

        initStandardOperations();
    }

    @Override
    public SolverResult solve(Constraint constraint) 
    {
        if (null == constraint)
            throw new NullPointerException();

        if (!isSupported(constraint.getKind()))
            throw new IllegalArgumentException(String.format(UNSUPPORTED_KIND_ERR,
                constraint.getKind().getClass().getSimpleName(), constraint.getKind()));

        final SolverResultBuilder resultBuilder = 
            new SolverResultBuilder(SolverResult.Status.ERROR);

        try
        {
            final SMTTextBuilder smtTextBuilder =
                new SMTTextBuilder(constraint.getVariables(), getOperations());

            final Walker walker = new Walker(smtTextBuilder);
            walker.visit(((Formulas) constraint.getInnerRep()).exprs());

            final String tempFile = File.createTempFile(TEMP_FILE, TEMP_FILE_SUFFIX).getPath();
            smtTextBuilder.saveToFile(tempFile);

            final Process process = runSolver(Environment.getSolverPath(), tempFile, "");
            final BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()));

            final Iterator<Variable> vi = constraint.getUnknownVariables().iterator();
            boolean isStatusSet = false;  

            String line;
            final Map<String, Variable> refs = new HashMap<String, Variable>();

            while((line = reader.readLine()) != null)
            {
                if (!isStatusSet && tryToParseStatus(line, resultBuilder))
                {
                    isStatusSet = true;
                }
                else if (tryToParseError(line, resultBuilder))
                {
                    // Do nothing
                }
                else if (vi.hasNext() && tryToParseVariable(line, vi.next(), resultBuilder, refs))
                {
                    // Do nothing
                }
                else if (tryToParseModel(line, reader, refs, resultBuilder))
                    ; // Do nothing
                else
                {
                    assert false : String.format(UNK_OUTPUT_ERR_FRMT, line);
                    resultBuilder.addError(String.format(UNK_OUTPUT_ERR_FRMT, line));
                }
            }
        }
        catch (IOException e)
        {
            resultBuilder.setStatus(SolverResult.Status.ERROR);
            resultBuilder.addError(IO_EXCEPTION_ERR + e.getMessage());
        }

        return resultBuilder.build();
    }

    private Process runSolver(String solverPath, String constraintFileName, String solverArgs) throws IOException
    {
        final ProcessBuilder pb = new ProcessBuilder(solverPath, constraintFileName, solverArgs);
        return pb.start();
    }

    private static boolean tryToParseStatus(String line, SolverResultBuilder resultBuilder)
    {
        final Matcher matcher = Pattern.compile(SMTRegExp.STATUS_PTRN).matcher(line);

        if (!matcher.matches())
            return false;

        if (line.equals(SMTRegExp.SAT))
            resultBuilder.setStatus(SolverResult.Status.SAT);
        else if (line.equals(SMTRegExp.UNSAT))
            resultBuilder.setStatus(SolverResult.Status.UNSAT);
        else
            resultBuilder.setStatus(SolverResult.Status.UNKNOWN);

        return true;
    }

    private static boolean tryToParseError(String line, SolverResultBuilder resultBuilder)
    {
        final Matcher matcher = Pattern.compile(SMTRegExp.ERR_PTRN).matcher(line);

        if (!matcher.matches())
            return false;
        
        resultBuilder.addError(matcher.group().replaceAll(SMTRegExp.ERR_TRIM_PTRN, ""));
        return true;
    }

    private static Variable parseVariable(String name, DataType typeInfo, String valueText)
    {
        final int radix;

        if (Pattern.compile(SMTRegExp.LINE_START + SMTRegExp.VALUE_BIN).matcher(valueText).matches())
            radix = 2;
        else if (Pattern.compile(SMTRegExp.LINE_START + SMTRegExp.VALUE_HEX).matcher(valueText).matches())
            radix = 16;
        else
            radix = 10; // decimal value by default

        final Data data = 
            typeInfo.valueOf(valueText.replaceAll(SMTRegExp.VALUE_TRIM_PTRN, ""), radix);

        return new Variable(name, data);
    }

    private static boolean tryToParseVariable(String line, Variable variable, SolverResultBuilder resultBuilder, Map<String, Variable> refs)
    {
        final Matcher matcher = 
            Pattern.compile(String.format(SMTRegExp.EXPR_PTRN_FRMT, variable.getName())).matcher(line);

        if (!matcher.matches())
            return false;

        final String valueText = 
            matcher.group().replaceAll(String.format(SMTRegExp.EXPR_TRIM_PTRN_FRMT, variable.getName()), "");
        final Matcher refMatcher =
            Pattern.compile(SMTRegExp.ARRAY_REF).matcher(valueText);
        if (refMatcher.matches())
            refs.put(refMatcher.group(1), variable);
        else
            resultBuilder.addVariable(
                parseVariable(variable.getName(), variable.getData().getType(), valueText));

        return true;
    }

    private static boolean tryToParseModel(
        String line,
        BufferedReader reader,
        Map<String, Variable> refs,
        SolverResultBuilder builder) throws IOException
    {
        if (!line.equals("(model "))
            return false;
        // skip model when there are no deferred variables
        if (refs.isEmpty())
        {
            while (!reader.readLine().equals(")"))
                ; // skip line
            return true;
        }

        final Pattern defPattern =
            Pattern.compile("[ ]*\\(define-fun[ ]([^ ]+)[ ].*");
        final Map<String, List<String>> model =
            new HashMap<String, List<String>>();

        line = reader.readLine();
        final Matcher matcher = defPattern.matcher(line);

        List<String> lines = null;
        for (; !line.equals(")"); line = reader.readLine())
            if (matcher.reset(line).matches())
            {
                lines = new ArrayList<String>();
                model.put(matcher.group(1), lines);
            }
            else
                lines.add(line.trim());

        final Map<String, String> valueTextCache =
            new HashMap<String, String>();

        for (Map.Entry<String, Variable> ref : refs.entrySet())
        {
            final String valueText = arrayModelToText(ref.getKey(), model, valueTextCache);
            // FIXME radix?
            builder.addVariable(new Variable(
                ref.getValue().getName(),
                ref.getValue().getData().getType().valueOf(valueText, 10)));
        }
        return true;
    }

    private static String arrayModelToText(String name, Map<String, List<String>> model, Map<String, String> cache)
    {
        /*
            Build text representation that valueOf() can deal with
        */

        if (cache.containsKey(name))
            return cache.get(name);

        final StringBuilder builder = new StringBuilder();
        builder.append("(");

        final Matcher entryMatcher =
            Pattern.compile("\\(ite[ ]\\(=[ ][^ ]+[ ](.+)\\)+[ ](.+)").matcher("");

        final Matcher arrayRefMatcher =
            Pattern.compile(SMTRegExp.ARRAY_REF).matcher("");

        final List<String> entries = model.get(name);
        for (String entry : entries)
            if (entryMatcher.reset(entry).matches())
            {
                String key = entryMatcher.group(1);
                if (key.charAt(0) == '(')
                    key = key.substring(1, key.length() - 1);
                if (arrayRefMatcher.reset(key).matches())
                    key = arrayModelToText(arrayRefMatcher.group(1), model, cache);

                String value = entryMatcher.group(2);
                if (value.charAt(0) == '(')
                    value = value.substring(1, value.length() - 1);
                if (arrayRefMatcher.reset(value).matches())
                    value = arrayModelToText(arrayRefMatcher.group(1), model, cache);

                builder.append("(").append(key).append(":").append(value).append(")");
            }

        builder.append(")");
        final String s = builder.toString();
        cache.put(name, s);
        return s;
    }

    private void initStandardOperations()
    {
        /*  Logic Operations */
        addStandardOperation(StandardOperation.EQ,        "=");
        addStandardOperation(StandardOperation.NOTEQ,     "distinct");
        addStandardOperation(StandardOperation.EQCASE,    "=");
        addStandardOperation(StandardOperation.NOTEQCASE, "distinct");
        addStandardOperation(StandardOperation.AND,       "and");
        addStandardOperation(StandardOperation.OR,        "or");
        addStandardOperation(StandardOperation.NOT,       "not");
        addStandardOperation(StandardOperation.XOR,       "xor");
        addStandardOperation(StandardOperation.IMPL,      "=>");
        addStandardOperation(StandardOperation.ITE,       "ite");

        //Logic arithmetic
        addStandardOperation(StandardOperation.MINUS,     "-");
        addStandardOperation(StandardOperation.PLUS,      "+");
        addStandardOperation(StandardOperation.ADD,       "+");
        addStandardOperation(StandardOperation.SUB,       "-");
        addStandardOperation(StandardOperation.MUL,       "*");
        addStandardOperation(StandardOperation.DIV,       "div");
        addStandardOperation(StandardOperation.REM,       "rem");
        addStandardOperation(StandardOperation.MOD,       "mod");
        addStandardOperation(StandardOperation.GREATER,   ">");
        addStandardOperation(StandardOperation.GREATEREQ, ">=");
        addStandardOperation(StandardOperation.LESS,      "<");
        addStandardOperation(StandardOperation.LESSEQ,    "<=");
        addStandardOperation(StandardOperation.POWER,     "^");

        /* Bitvector operations */

        // Basic Bitvector Arithmetic
        addStandardOperation(StandardOperation.BVADD,     "bvadd");
        addStandardOperation(StandardOperation.BVSUB,     "bvsub");
        addStandardOperation(StandardOperation.BVNEG,     "bvneg");
        addStandardOperation(StandardOperation.BVMUL,     "bvmul");
        addStandardOperation(StandardOperation.BVUREM,    "bvurem");
        addStandardOperation(StandardOperation.BVSREM,    "bvsrem");
        addStandardOperation(StandardOperation.BVSMOD,    "bvsmod");
        addStandardOperation(StandardOperation.BVLSHL,    "bvshl");
        addStandardOperation(StandardOperation.BVASHL,    "bvshl");
        addStandardOperation(StandardOperation.BVLSHR,    "bvlshr");
        addStandardOperation(StandardOperation.BVASHR,    "bvashr");
        addStandardOperation(StandardOperation.BVCONCAT,  "concat");
        addStandardOperation(StandardOperation.BVREPEAT,  "repeat");
        addStandardOperation(StandardOperation.BVROL,     "rotate_left");
        addStandardOperation(StandardOperation.BVROR,     "rotate_right");
        addStandardOperation(StandardOperation.BVZEROEXT, "extend_zero");
        addStandardOperation(StandardOperation.BVSIGNEXT, "extend_sign");

        // Bitwise Operations
        addStandardOperation(StandardOperation.BVOR,   "bvor");
        addStandardOperation(StandardOperation.BVXOR,  "bvxor");
        addStandardOperation(StandardOperation.BVAND,  "bvand");
        addStandardOperation(StandardOperation.BVNOT,  "bvnot");
        addStandardOperation(StandardOperation.BVNAND, "bvnand");
        addStandardOperation(StandardOperation.BVNOR,  "bvnor");
        addStandardOperation(StandardOperation.BVXNOR, "bvxnor");

        // Predicates over Bitvectors
        addStandardOperation(StandardOperation.BVULE,  "bvule");
        addStandardOperation(StandardOperation.BVULT,  "bvult");
        addStandardOperation(StandardOperation.BVUGE,  "bvuge");
        addStandardOperation(StandardOperation.BVUGT,  "bvugt");
        addStandardOperation(StandardOperation.BVSLE,  "bvsle");
        addStandardOperation(StandardOperation.BVSLT,  "bvslt");
        addStandardOperation(StandardOperation.BVSGE,  "bvsge");
        addStandardOperation(StandardOperation.BVSGT,  "bvsgt");

        /* Array operations */
        addStandardOperation(StandardOperation.SELECT, "select");
        addStandardOperation(StandardOperation.STORE,  "store");
    }
}
