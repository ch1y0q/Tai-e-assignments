/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // first called by analyzer
        CPFact ret = new CPFact();

        for (Var param : cfg.getMethod().getIR().getParams()) {
            if (canHoldInt(param)) ret.update(param, Value.getNAC());
        }

        return ret;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        for (Var var : fact.keySet()) {
            if (canHoldInt(var)) target.update(var, meetValue(target.get(var), fact.get(var)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // slides: ch6 pp.238
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }
        if (v1.isUndef() && v2.isConstant()) {
            return Value.makeConstant(v2.getConstant());
        }
        if (v2.isUndef() && v1.isConstant()) {
            return Value.makeConstant(v1.getConstant());
        }
        if (v1.isUndef() && v2.isUndef()) {
            return Value.getUndef();
        }
        if (v1.getConstant() != v2.getConstant()) {
            return Value.getNAC();
        }
        return Value.makeConstant(v1.getConstant());  // v1 == v2 == constant

    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // slides: ch6 pp.247
        if (stmt instanceof DefinitionStmt<?, ?> defStmt) { // is assign statement
            LValue lValue = defStmt.getLValue();
            Exp rValue = defStmt.getRValue();

            if (lValue instanceof Var && canHoldInt((Var) lValue)) {
                boolean modified;
                modified = out.copyFrom(in);
                // out.update((Var) lValue, Value.getUndef()); // delete existing LHS; no need
                modified |= out.update((Var) lValue, evaluate(rValue, in));
                return modified;
            }

        }
        // is not assign statement, use identity function
        return out.copyFrom(in);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof IntLiteral) {
            return Value.makeConstant(((IntLiteral) exp).getValue());
        }
        if (exp instanceof Var) {
            if (canHoldInt((Var) exp)) {
                if (in.get((Var) exp).isConstant()) {
                    return Value.makeConstant(in.get((Var) exp).getConstant());
                }
                if (in.get((Var) exp).isUndef()) {
                    return Value.getUndef();
                }
                if (in.get((Var) exp).isNAC()) {
                    return Value.getNAC();
                }
            } else {
                return Value.getUndef();  // return UNDEF for unsupported type
            }
        }
        if (exp instanceof BinaryExp binaryExp) {
            Var op1 = binaryExp.getOperand1();
            Var op2 = binaryExp.getOperand2();

            int v1 = Integer.MAX_VALUE, v2 = Integer.MAX_VALUE;
            boolean valid1 = false, valid2 = false;
            if (canHoldInt(op1)) {
                if (in.get(op1).isConstant()) {
                    v1 = in.get(op1).getConstant();
                    valid1 = true;
                }
            }

            if (canHoldInt(op2)) {
                if (in.get(op2).isConstant()) {
                    v2 = in.get(op2).getConstant();
                    valid2 = true;
                }
            }

            if (valid1 && valid2) {
                if (binaryExp instanceof ArithmeticExp arithmeticExp) {

                    switch (arithmeticExp.getOperator()) {
                        case ADD -> {
                            return Value.makeConstant(v1 + v2);
                        }
                        case SUB -> {
                            return Value.makeConstant(v1 - v2);
                        }
                        case MUL -> {
                            return Value.makeConstant(v1 * v2);
                        }
                        case DIV -> {
                            if (v2 == 0) return Value.getUndef();
                            return Value.makeConstant(v1 / v2);
                        }
                        case REM -> {
                            if (v2 == 0) return Value.getUndef();
                            return Value.makeConstant(v1 % v2);
                        }
                    }
                }
                if (binaryExp instanceof BitwiseExp) {
                    switch (((BitwiseExp) binaryExp).getOperator()) {
                        case OR -> {
                            return Value.makeConstant(v1 | v2);
                        }
                        case AND -> {
                            return Value.makeConstant(v1 & v2);
                        }
                        case XOR -> {
                            return Value.makeConstant(v1 ^ v2);
                        }
                    }
                }
                if (binaryExp instanceof ConditionExp) {
                    switch (((ConditionExp) binaryExp).getOperator()) {
                        case EQ -> {
                            return Value.makeConstant(v1 == v2 ? 1 : 0);
                        }
                        case GE -> {
                            return Value.makeConstant(v1 >= v2 ? 1 : 0);
                        }
                        case GT -> {
                            return Value.makeConstant(v1 > v2 ? 1 : 0);
                        }
                        case NE -> {
                            return Value.makeConstant(v1 != v2 ? 1 : 0);
                        }
                        case LE -> {
                            return Value.makeConstant(v1 <= v2 ? 1 : 0);
                        }
                        case LT -> {
                            return Value.makeConstant(v1 < v2 ? 1 : 0);
                        }
                    }
                }
                if (binaryExp instanceof ShiftExp) {
                    switch (((ShiftExp) binaryExp).getOperator()) {
                        case SHL -> {
                            return Value.makeConstant(v1 << v2);
                        }
                        case SHR -> {
                            return Value.makeConstant(v1 >> v2);
                        }
                        case USHR -> {
                            return Value.makeConstant(v1 >>> v2);
                        }
                    }
                }
            }

            // special case: 0 * NAC/UNDEF = 0
            /* BUT WILL NOT PASS OJ!
            if (valid1 && v1 == 0 || valid2 && v2 == 0) {
                if (binaryExp instanceof ArithmeticExp arithmeticExp){
                    if(arithmeticExp.getOperator() == ArithmeticExp.Op.MUL){
                        return Value.makeConstant(0);
                    }
                }
            }
            */

            // special case: NAC/UNDEF DIV/REM 0 = UNDEF
            if (valid2 && v2 == 0 && exp instanceof ArithmeticExp arithmeticExp) {
                if (arithmeticExp.getOperator() == ArithmeticExp.Op.DIV || arithmeticExp.getOperator() == ArithmeticExp.Op.REM)
                    return Value.getUndef();
            }

            if (in.get(op1).isNAC() || in.get(op2).isNAC()) {
                return Value.getNAC();
            }

            // ignore Var that cannot hold int
            return Value.getUndef();
        }

        /* no need to consider type casting for now
        if (exp instanceof CastExp castExp) {
            if (in.get(castExp.getValue()).isUndef()) {
                return Value.getUndef();
            }
            if (in.get(castExp.getValue()).isNAC()) {
                return Value.getNAC();
            }
            if (canHoldInt(castExp.getValue())) {
                int beforeCast = in.get(castExp.getValue()).getConstant();
                if (castExp.getCastType() instanceof PrimitiveType) {
                    switch ((PrimitiveType) castExp.getCastType()) {
                        case BYTE:
                            return Value.makeConstant((byte) beforeCast);
                        case SHORT:
                            return Value.makeConstant((short) beforeCast);
                        case INT:
                            return Value.makeConstant((int) beforeCast);
                        case CHAR:
                            return Value.makeConstant((char) beforeCast);
                        case BOOLEAN:
                            return Value.makeConstant(beforeCast == 0 ? 0 : 1);
                    }

                }
                return Value.makeConstant(beforeCast);
            } else {
                return Value.getNAC();
            }

        }
        */

        return Value.getNAC();
    }
}
