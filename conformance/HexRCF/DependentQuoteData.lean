/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public section

/-! Public dependent readers whose Boolean boundary is available only through
an equation. The nested reader retains both branch-equality proofs. -/

namespace Hex.RCF.DependentQuote

def gate : Bool := true

private theorem gate_proof : gate = true := rfl

theorem gate_eq : gate = true := gate_proof

@[expose] def input : Option Nat := if gate then some 7 else none

theorem input_value {n : Nat} (h : input = some n) : n = 7 := by
  have exactInput : input = some 7 := by simp [input,gate_eq]
  exact (Option.some.inj (exactInput.symm.trans h)).symm

@[expose] def reader : Option {n : Nat // n = 7} :=
  match h : input with
  | none => none
  | some n => some ⟨n,input_value h⟩

@[expose] def nested : Option {p : Nat × Nat // p.1 = 7 ∧ p.2 = 7} :=
  match h : input with
  | none => none
  | some n =>
    match k : input with
    | none => none
    | some m => some ⟨(n,m),input_value h,input_value k⟩

@[expose] def unsupported : Option {n : Nat // n = 7} :=
  (match h : input with
  | none => fun (_ : Nat) => (none : Option {n : Nat // n = 7})
  | some n => fun (_ : Nat) => (some ⟨n,input_value h⟩ : Option {n : Nat // n = 7})) 2

end Hex.RCF.DependentQuote
