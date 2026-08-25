/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexMvGcd.ComparatorCases
import LeanBench

/-!
Fixed external-comparator registrations for the seven Phase-4 input families.

Every named point has a Hex, python-flint, and Singular arm. The process-call
arms discard one warmup invocation so driver and CAS startup are outside the
timed repetitions; the Hex arm uses the same shape so lazy input construction
is likewise outside timing. `compare` joins each triple by its output hash.
-/

namespace Hex.MvGcdBench.ComparatorCases

def config (family implementation : String)
    (expectedHash : UInt64) : LeanBench.FixedBenchmarkConfig :=
  { repeats := 3, maxSecondsPerCall := 10.0, minTotalSeconds := 0.2,
    warmupFirstIter := true,
    expectedHash := some expectedHash,
    tags := #["mv-gcd-comparator", family, implementation] }

/-! `coprime-pairs` -/

setup_fixed_benchmark runLeanCoprimeDense2 where
  config "coprime-pairs" "lean" 0x227808efbc4a0df6
setup_fixed_benchmark runFlintCoprimeDense2 where
  config "coprime-pairs" "flint" 0x227808efbc4a0df6
setup_fixed_benchmark runSingularCoprimeDense2 where
  config "coprime-pairs" "singular" 0x227808efbc4a0df6
setup_fixed_benchmark runLeanCoprimeSparse8 where
  config "coprime-pairs" "lean" 0xc81d2f17120678a5
setup_fixed_benchmark runFlintCoprimeSparse8 where
  config "coprime-pairs" "flint" 0xc81d2f17120678a5
setup_fixed_benchmark runSingularCoprimeSparse8 where
  config "coprime-pairs" "singular" 0xc81d2f17120678a5

/-! `dense-gcds` -/

setup_fixed_benchmark runLeanDense3d5 where
  config "dense-gcds" "lean" 0x54b3f437e9d29507
setup_fixed_benchmark runFlintDense3d5 where
  config "dense-gcds" "flint" 0x54b3f437e9d29507
setup_fixed_benchmark runSingularDense3d5 where
  config "dense-gcds" "singular" 0x54b3f437e9d29507
setup_fixed_benchmark runLeanDense4d5 where
  config "dense-gcds" "lean" 0x194ca12395aa1c60
setup_fixed_benchmark runFlintDense4d5 where
  config "dense-gcds" "flint" 0x194ca12395aa1c60
setup_fixed_benchmark runSingularDense4d5 where
  config "dense-gcds" "singular" 0x194ca12395aa1c60

/-! `sparse-stress` -/

setup_fixed_benchmark runLeanSparse5d4 where
  config "sparse-stress" "lean" 0xf3af0d107878de6b
setup_fixed_benchmark runFlintSparse5d4 where
  config "sparse-stress" "flint" 0xf3af0d107878de6b
setup_fixed_benchmark runSingularSparse5d4 where
  config "sparse-stress" "singular" 0xf3af0d107878de6b
setup_fixed_benchmark runLeanSparse5d16 where
  config "sparse-stress" "lean" 0xf3af0d107878de6b
setup_fixed_benchmark runFlintSparse5d16 where
  config "sparse-stress" "flint" 0xf3af0d107878de6b
setup_fixed_benchmark runSingularSparse5d16 where
  config "sparse-stress" "singular" 0xf3af0d107878de6b

/-! `swell` -/

setup_fixed_benchmark runLeanSwell3 where
  config "swell" "lean" 0x3f55cf2c712015fc
setup_fixed_benchmark runFlintSwell3 where
  config "swell" "flint" 0x3f55cf2c712015fc
setup_fixed_benchmark runSingularSwell3 where
  config "swell" "singular" 0x3f55cf2c712015fc
setup_fixed_benchmark runLeanSwell5 where
  config "swell" "lean" 0x3f55cf2c712015fc
setup_fixed_benchmark runFlintSwell5 where
  config "swell" "flint" 0x3f55cf2c712015fc
setup_fixed_benchmark runSingularSwell5 where
  config "swell" "singular" 0x3f55cf2c712015fc

/-! `rational` -/

setup_fixed_benchmark runLeanRational3d5 where
  config "rational" "lean" 0xe4e174072095f1f2
setup_fixed_benchmark runFlintRational3d5 where
  config "rational" "flint" 0xe4e174072095f1f2
setup_fixed_benchmark runSingularRational3d5 where
  config "rational" "singular" 0xe4e174072095f1f2
setup_fixed_benchmark runLeanRational4d5 where
  config "rational" "lean" 0xb0ea89a0bf1eb33c
setup_fixed_benchmark runFlintRational4d5 where
  config "rational" "flint" 0xb0ea89a0bf1eb33c
setup_fixed_benchmark runSingularRational4d5 where
  config "rational" "singular" 0xb0ea89a0bf1eb33c

/-! `squarefree` -/

setup_fixed_benchmark runLeanSquarefree2m1 where
  config "squarefree" "lean" 0xde0a944a81313c66
setup_fixed_benchmark runFlintSquarefree2m1 where
  config "squarefree" "flint" 0xde0a944a81313c66
setup_fixed_benchmark runSingularSquarefree2m1 where
  config "squarefree" "singular" 0xde0a944a81313c66
setup_fixed_benchmark runLeanSquarefree4m7 where
  config "squarefree" "lean" 0x9834ad9417326d80
setup_fixed_benchmark runFlintSquarefree4m7 where
  config "squarefree" "flint" 0x9834ad9417326d80
setup_fixed_benchmark runSingularSquarefree4m7 where
  config "squarefree" "singular" 0x9834ad9417326d80

/-! `cofactor-heavy` -/

setup_fixed_benchmark runLeanCofactor16 where
  config "cofactor-heavy" "lean" 0x7c3948af38b08ac0
setup_fixed_benchmark runFlintCofactor16 where
  config "cofactor-heavy" "flint" 0x7c3948af38b08ac0
setup_fixed_benchmark runSingularCofactor16 where
  config "cofactor-heavy" "singular" 0x7c3948af38b08ac0
setup_fixed_benchmark runLeanCofactor64 where
  config "cofactor-heavy" "lean" 0xb1205f7d916b1032
setup_fixed_benchmark runFlintCofactor64 where
  config "cofactor-heavy" "flint" 0xb1205f7d916b1032
setup_fixed_benchmark runSingularCofactor64 where
  config "cofactor-heavy" "singular" 0xb1205f7d916b1032

end Hex.MvGcdBench.ComparatorCases
