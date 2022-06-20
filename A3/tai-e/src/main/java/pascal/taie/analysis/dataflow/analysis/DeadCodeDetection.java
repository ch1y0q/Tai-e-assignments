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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.CastExp;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.NewExp;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.util.collection.Pair;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));

        // deadCode <- all the statements
        // BFS starting from CFG entry
        // remove each reachable statement from deadCode
        // then check if the statement is dead code assignment, if so, re-add to deadCode
        // then traverse all possible out-edges of the statement

        // control-flow unreachable

        deadCode.addAll(cfg.getIR().getStmts());

        Queue<Stmt> controlFlowReachable = new LinkedList<>();
        controlFlowReachable.add(cfg.getEntry());

        queueLoop:
        while (!controlFlowReachable.isEmpty()) {
            Stmt cur = controlFlowReachable.remove();
            deadCode.remove(cur);
            // unreachable branch
            if (cfg.isExit(cur)) {
                continue queueLoop;
            }
            if (cur instanceof If ifs) {
                Value conditionValue = ConstantPropagation.evaluate(ifs.getCondition(), constants.getInFact(cur));
                if (conditionValue.isConstant()) {
                    Set<Edge<Stmt>> edges = cfg.getOutEdgesOf(cur);
                    if (conditionValue.getConstant() == 1) {  // true
                        if (deadCode.contains(ifs.getTarget())) {
                            controlFlowReachable.add(ifs.getTarget());
                        }
                        continue queueLoop;
                    } else if (conditionValue.getConstant() == 0) {  // false
                        edges.forEach(branch -> {
                            if (branch.getKind() == Edge.Kind.IF_FALSE && deadCode.contains(branch.getTarget())) {
                                controlFlowReachable.add(branch.getTarget());
                            }
                        });
                    }
                    continue queueLoop;
                }
            }
            if (cur instanceof SwitchStmt switchStmt) {
                Value conditionValue = ConstantPropagation.evaluate(switchStmt.getVar(), constants.getInFact(cur));
                if (conditionValue.isConstant()) {
                    // not in of cases, default branch
                    if (!switchStmt.getCaseValues().contains(conditionValue.getConstant())) {
                        if (deadCode.contains(switchStmt.getDefaultTarget())) {
                            controlFlowReachable.add(switchStmt.getDefaultTarget());
                        }

                        continue queueLoop;
                    }
                    // check each of the cases
                    for (Pair<Integer, Stmt> pair : switchStmt.getCaseTargets()) {

                        if (conditionValue.getConstant() == pair.first()) {
                            if (deadCode.contains(pair.second())) {
                                controlFlowReachable.add(pair.second());
                            }
                            continue queueLoop;
                        }
                    }
                }
            }

            if (cur instanceof AssignStmt assignStmt && hasNoSideEffect(assignStmt.getRValue())) {
                // dead variable assignment
                if (assignStmt.getLValue() instanceof Var && !liveVars.getOutFact(cur).contains((Var) assignStmt.getLValue())) {
                    deadCode.add(cur);
                }
            }

            // none of if(constant) or switch(constant) or return
            cfg.getOutEdgesOf(cur).forEach(outEdge -> controlFlowReachable.add(outEdge.getTarget()));

        }

        // Your task is to recognize dead code in ir and add it to deadCode
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
