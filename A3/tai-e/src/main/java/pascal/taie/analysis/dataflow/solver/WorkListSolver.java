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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.*;
import java.util.concurrent.LinkedBlockingDeque;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // slides ch.6 pp.258
        Queue<Node> worklist = new LinkedBlockingDeque<>();
        for (Node node : cfg) {
            worklist.add(node);
        }

        while (!worklist.isEmpty()) {
            Node cur = worklist.remove();
            // slides: ch6 pp.255 (Non-distributivity), no need for now
            // slides: ch6 pp.259
            for (Node pred : cfg.getPredsOf(cur)) {
                analysis.meetInto(result.getOutFact(pred), result.getInFact(cur));
            }

            if (analysis.transferNode(cur, result.getInFact(cur), result.getOutFact(cur))) {
                worklist.addAll(cfg.getSuccsOf(cur));
            }

        }

    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        Queue<Node> worklist = new LinkedBlockingDeque<>();
        for (Node node : cfg) {
            worklist.add(node);
        }

        while (!worklist.isEmpty()) {
            Node cur = worklist.remove();
            // slides: ch6 pp.255 (Non-distributivity), no need for now
            // slides: ch6 pp.259
            for (Node succ : cfg.getSuccsOf(cur)) {
                analysis.meetInto(result.getInFact(succ), result.getOutFact(cur));
            }

            if (analysis.transferNode(cur, result.getInFact(cur), result.getOutFact(cur))) {
                worklist.addAll(cfg.getPredsOf(cur));
            }

        }
    }
}
