/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntFactor.Construction
import HexIntFactor.FieldReplay
import LeanBench

/-! Fixed native construction and checker observations for the explicit ECM
provider. The input references prevent closed-term lifting. Search includes the
final compiled self-check; the checker targets use the exact emitted literals. -/

namespace Hex.IntFactorFields
open Hex.Nat

private instance : Nonempty PrimeCert := ⟨.small 2⟩

private initialize secpRef : IO.Ref PrimeCert ← IO.mkRef secp256k1
private initialize p384Ref : IO.Ref PrimeCert ← IO.mkRef p384
private initialize curveRef : IO.Ref PrimeCert ← IO.mkRef curve448

private def construct (ref : IO.Ref PrimeCert) : IO Nat := do
  let n := (← ref.get).subject
  match Construction.run n (Hex.Rand.ofSeed n) constructionBudget ecmFactorSearch with
  | .ok success => return success.attempts
  | .error _ => return 0

private def replay (ref : IO.Ref PrimeCert) : IO Nat := do
  return if checkPrime (← ref.get) then 1 else 0

def runSecpConstruction (_ : Unit) : IO Nat := construct secpRef
def runP384Construction (_ : Unit) : IO Nat := construct p384Ref
def runCurve448Construction (_ : Unit) : IO Nat := construct curveRef
def runSecpChecker (_ : Unit) : IO Nat := replay secpRef
def runP384Checker (_ : Unit) : IO Nat := replay p384Ref
def runCurve448Checker (_ : Unit) : IO Nat := replay curveRef

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
setup_fixed_benchmark runSecpChecker where {
  repeats := 5
  maxSecondsPerCall := 5.0
  expectedHash := some (Hashable.hash (1 : Nat))
}
setup_fixed_benchmark runP384Checker where {
  repeats := 5
  maxSecondsPerCall := 5.0
  expectedHash := some (Hashable.hash (1 : Nat))
}
setup_fixed_benchmark runCurve448Checker where {
  repeats := 5
  maxSecondsPerCall := 5.0
  expectedHash := some (Hashable.hash (1 : Nat))
}

end Hex.IntFactorFields
