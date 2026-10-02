/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRowReduceMathlib.Tactic

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option profiler true
set_option profiler.threshold 1000000
set_option trace.HexMatrix.certificate true

noncomputable def result := solve% (!![(10005885459072874282980055070499143616 / 17014118346046923173168730371588410573), (10005885459072874282980055070499143616 / 17014118346046923173168730371588410573); (10005885459072874282980055070499143616 / 17014118346046923173168730371588410573), (10005885459072874282980055070499143616 / 17014118346046923173168730371588410573)] : Matrix (Fin 2) (Fin 2) ℚ) ![0, 0]

#print axioms result
