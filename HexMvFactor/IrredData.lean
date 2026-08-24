/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvFactor.Decomp

@[expose] public section

/-! Data shared by irreducibility replay and the Kronecker producer. -/

namespace Hex.MvFactor

open Hex
open Hex.MvPoly

/-- A checkable irreducibility witness, modulo the univariate obligations
reported by `obligations`. -/
inductive IrredCert :
    (n : Nat) → (cmp : Mono n → Mono n → Ordering) →
    [Std.TransCmp cmp] → [Std.LawfulEqCmp cmp] → Type 1
  | degreeOne {n : Nat}
      {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
      [outerTrans : Std.TransCmp cmp] [outerEq : Std.LawfulEqCmp cmp]
      (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
      [order : IsMonomialOrder cmp']
      (prim : ContentCert n Int cmp') :
      @IrredCert (n + 1) cmp outerTrans outerEq
  | image {n : Nat}
      {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
      [outerTrans : Std.TransCmp cmp] [outerEq : Std.LawfulEqCmp cmp]
      (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
      [order : IsMonomialOrder cmp'] (point : Fin n → Int)
      (prim : ContentCert n Int cmp') :
      @IrredCert (n + 1) cmp outerTrans outerEq
  | embed {n : Nat}
      {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
      [outerTrans : Std.TransCmp cmp] [outerEq : Std.LawfulEqCmp cmp]
      (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
      [order : IsMonomialOrder cmp'] (sub : MvPoly n Int cmp')
      (cert : IrredCert n cmp') :
      @IrredCert (n + 1) cmp outerTrans outerEq
  | kronecker {n : Nat} {cmp : Mono n → Mono n → Ordering}
      [outerTrans : Std.TransCmp cmp] [outerEq : Std.LawfulEqCmp cmp]
      (scalar : Int) (uni : List (ZPoly × Nat)) :
      @IrredCert n cmp outerTrans outerEq

/-- A proposed nontrivial factorization into two factors. -/
structure Split (n : Nat) (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] where
  left : MvPoly n Int cmp
  right : MvPoly n Int cmp

/-- A decomposition paired positionally with irreducibility certificates. -/
structure Complete (n : Nat) (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] where
  decomp : Decomp n cmp
  certs : List (IrredCert n cmp)

/-- The total outcome of the Kronecker sweep. -/
inductive Verdict (n : Nat) (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] : Type 1
  | irreducible (cert : IrredCert n cmp)
  | reducible (split : Split n cmp)

end Hex.MvFactor
