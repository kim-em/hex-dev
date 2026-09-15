/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPolyMathlib.KernelResidue

public section

/-! Consumer-side elaboration and semantic replay over Mathlib residues. -/

namespace HexMvPolyMathlib.KernelResidueTests

open Hex.MvPoly.Kernel

local instance : Hex.ZMod64.Bounds 5 := ⟨by decide, by decide⟩

@[expose] def a : PolyList Nat := [([1, 0], 4), ([0, 1], 2)]
@[expose] def square : PolyList Nat := [([2, 0], 1), ([1, 1], 1), ([0, 2], 4)]

private theorem canonicalA : CanonicalMod 5 2 a :=
  isCanonicalMod_iff.mp (by decide +kernel)
private theorem canonicalSquare : CanonicalMod 5 2 square :=
  isCanonicalMod_iff.mp (by decide +kernel)

example : Kernel.denoteMod 5 (cmp := Hex.Mono.lex) (n := 2) [] = 0 := Kernel.denoteMod_nil 5
example : Kernel.denoteMod 5 (cmp := Hex.Mono.lex) (n := 2) (oneMod 5 2) = 1 :=
  Kernel.denoteMod_oneMod 5

example : Kernel.denoteMod 5 (cmp := Hex.Mono.lex) (n := 2) (addMod 5 a a) =
    Kernel.denoteMod 5 (cmp := Hex.Mono.lex) a + Kernel.denoteMod 5 (cmp := Hex.Mono.lex) a :=
  Kernel.denoteMod_addMod 5 canonicalA canonicalA

example : Kernel.denoteMod 5 (cmp := Hex.Mono.lex) (n := 2) (mulMod 5 a a) =
    Kernel.denoteMod 5 (cmp := Hex.Mono.lex) a * Kernel.denoteMod 5 (cmp := Hex.Mono.lex) a :=
  Kernel.denoteMod_mulMod 5 canonicalA canonicalA

example : Kernel.denoteMod 5 (cmp := Hex.Mono.lex) (n := 2) (subMod 5 a a) =
    Kernel.denoteMod 5 (cmp := Hex.Mono.lex) a - Kernel.denoteMod 5 (cmp := Hex.Mono.lex) a :=
  Kernel.denoteMod_subMod 5 canonicalA canonicalA

example : Kernel.denoteMod 5 (cmp := Hex.Mono.lex) (n := 2) (negMod 5 a) =
    -Kernel.denoteMod 5 (cmp := Hex.Mono.lex) a :=
  Kernel.denoteMod_negMod 5 canonicalA

example : Kernel.denoteMod 5 (cmp := Hex.Mono.lex) (n := 2) (smulMod 5 7 a) =
    MvPolynomial.C (7 : ZMod 5) * Kernel.denoteMod 5 (cmp := Hex.Mono.lex) a :=
  Kernel.denoteMod_smulMod 5 7 canonicalA

-- Kernel arithmetic identifies a supplied square, then the bridge turns that
-- certificate into a Mathlib polynomial multiplication identity.
example : Kernel.denoteMod 5 (cmp := Hex.Mono.grevlex) (n := 2) a *
    Kernel.denoteMod 5 (cmp := Hex.Mono.grevlex) a =
      Kernel.denoteMod 5 (cmp := Hex.Mono.grevlex) square := by
  rw [← Kernel.denoteMod_mulMod 5 canonicalA canonicalA]
  exact (Kernel.beq_mod_iff 5 (mulMod_canonical 5 canonicalA canonicalA)
    canonicalSquare).mp (by decide +kernel)

example : Kernel.denoteMod 5 (cmp := Hex.Mono.lex) (n := 2) (subMod 5 a a) = 0 :=
  (Kernel.isZero_mod_iff 5 (subMod_canonical 5 canonicalA canonicalA)).mp (by decide +kernel)

example (f : Hex.MvPoly 2 (Hex.ZMod64 5) Hex.Mono.grevlex) :
    Kernel.denoteMod 5 (cmp := Hex.Mono.grevlex) (ofResidues 5 (toList f)) =
      Kernel.residueEquiv 5 f := Kernel.denoteMod_ofResidues 5 f

section Trivial
local instance : Hex.ZMod64.Bounds 1 := ⟨by decide, by decide⟩

example : Kernel.denoteMod 1 (cmp := Hex.Mono.lex) (n := 2) (oneMod 1 2) = 1 :=
  Kernel.denoteMod_oneMod 1
end Trivial

end HexMvPolyMathlib.KernelResidueTests
