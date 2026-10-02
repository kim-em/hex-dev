/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexMinPolyMathlib.Tactic

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option profiler true
set_option profiler.threshold 1000000
set_option trace.HexMatrix.certificate true

theorem result : minpoly ℚ (!![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2076873887; 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -160577011; 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -789029286; 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1908603923; 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 291279004; 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1240370980; 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1147033662; 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1702612748; 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1147478241; 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 904861396; 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1404459872; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1117099764; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1178996020; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -887621950; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1552384262; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 74909512] : Matrix (Fin 16) (Fin 16) ℚ) =
    Polynomial.C 2076873887 + Polynomial.C 160577011 * Polynomial.X + Polynomial.C 789029286 * Polynomial.X ^ 2 + Polynomial.C 1908603923 * Polynomial.X ^ 3 + Polynomial.C (-291279004) * Polynomial.X ^ 4 + Polynomial.C 1240370980 * Polynomial.X ^ 5 + Polynomial.C 1147033662 * Polynomial.X ^ 6 + Polynomial.C (-1702612748) * Polynomial.X ^ 7 + Polynomial.C 1147478241 * Polynomial.X ^ 8 + Polynomial.C (-904861396) * Polynomial.X ^ 9 + Polynomial.C (-1404459872) * Polynomial.X ^ 10 + Polynomial.C 1117099764 * Polynomial.X ^ 11 + Polynomial.C 1178996020 * Polynomial.X ^ 12 + Polynomial.C 887621950 * Polynomial.X ^ 13 + Polynomial.C (-1552384262) * Polynomial.X ^ 14 + Polynomial.C (-74909512) * Polynomial.X ^ 15 + Polynomial.X ^ 16 := by min_poly

#print axioms result
