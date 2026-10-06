/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyDetMathlib

open Matrix

theorem HexPolyDetMathlib.ProofExamples.rankOne (x : Int) : Matrix.det !![1*1*x, 1*2*x, 1*3*x, 1*4*x, 1*5*x, 1*6*x, 1*7*x, 1*8*x, 1*9*x, 1*10*x; 2*1*x, 2*2*x, 2*3*x, 2*4*x, 2*5*x, 2*6*x, 2*7*x, 2*8*x, 2*9*x, 2*10*x; 3*1*x, 3*2*x, 3*3*x, 3*4*x, 3*5*x, 3*6*x, 3*7*x, 3*8*x, 3*9*x, 3*10*x; 4*1*x, 4*2*x, 4*3*x, 4*4*x, 4*5*x, 4*6*x, 4*7*x, 4*8*x, 4*9*x, 4*10*x; 5*1*x, 5*2*x, 5*3*x, 5*4*x, 5*5*x, 5*6*x, 5*7*x, 5*8*x, 5*9*x, 5*10*x; 6*1*x, 6*2*x, 6*3*x, 6*4*x, 6*5*x, 6*6*x, 6*7*x, 6*8*x, 6*9*x, 6*10*x; 7*1*x, 7*2*x, 7*3*x, 7*4*x, 7*5*x, 7*6*x, 7*7*x, 7*8*x, 7*9*x, 7*10*x; 8*1*x, 8*2*x, 8*3*x, 8*4*x, 8*5*x, 8*6*x, 8*7*x, 8*8*x, 8*9*x, 8*10*x; 9*1*x, 9*2*x, 9*3*x, 9*4*x, 9*5*x, 9*6*x, 9*7*x, 9*8*x, 9*9*x, 9*10*x; 10*1*x, 10*2*x, 10*3*x, 10*4*x, 10*5*x, 10*6*x, 10*7*x, 10*8*x, 10*9*x, 10*10*x] = 0 := by
  det

/-- info: 'HexPolyDetMathlib.ProofExamples.rankOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HexPolyDetMathlib.ProofExamples.rankOne
