/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntFactor.FieldBench
import LeanBench

/-! Manual native construction benchmarks. Full searches are excluded from the
routine smoke gate; the ordinary benchmark retains the three checker targets. -/

namespace Hex.IntFactorFields

setup_fixed_benchmark runSecpConstruction where {
  repeats := 5
  maxSecondsPerCall := 120.0
  expectedHash := some (Hashable.hash (145 : Nat))
}
setup_fixed_benchmark runP384Construction where {
  repeats := 5
  maxSecondsPerCall := 120.0
  expectedHash := some (Hashable.hash (290 : Nat))
}
setup_fixed_benchmark runCurve448Construction where {
  repeats := 5
  maxSecondsPerCall := 120.0
  expectedHash := some (Hashable.hash (259 : Nat))
}
end Hex.IntFactorFields

def main (args : List String) : IO UInt32 := LeanBench.Cli.dispatch args
