/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyFp.PrimeField

public section

namespace HexRationalFn.Conformance

scoped instance : Hex.ZMod64.Bounds 2 := ⟨by decide, by decide⟩
scoped instance : Hex.ZMod64.Bounds 7 := ⟨by decide, by decide⟩
scoped instance : Hex.ZMod64.PrimeModulus 2 := Hex.ZMod64.primeModulusOfPrime (by decide)
scoped instance : Hex.ZMod64.PrimeModulus 7 := Hex.ZMod64.primeModulusOfPrime (by decide)

end HexRationalFn.Conformance
