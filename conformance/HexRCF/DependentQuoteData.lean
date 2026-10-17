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

@[expose] def independent : Option {n : Nat // n = 7} :=
  (match h : input with
  | none => fun (_ : Nat) => (none : Option {n : Nat // n = 7})
  | some n => fun (_ : Nat) => (some ⟨n,input_value h⟩ : Option {n : Nat // n = 7})) 2

theorem value {n : Nat} (h : (if gate then some 7 else none) = some n) : n = 7 := by
  simpa only [gate_eq, Bool.true_eq, ite_true, Option.some.injEq] using h.symm

@[expose] def continued : Option {n : Nat // n = 7} :=
  match h : (if gate then some 7 else none) with
  | none => none
  | some n => if gate then some ⟨n,value h⟩ else none

def query : Option Nat := some 7
private theorem query_proof : query = some 7 := rfl
theorem query_eq : query = some 7 := query_proof
theorem query_value {n : Nat} (h : query = some n) : n = 7 :=
  (Option.some.inj (query_eq.symm.trans h)).symm
@[expose] def queried : Option {n : Nat // n = 7} :=
  match h : query with
  | none => none
  | some n => some ⟨n,query_value h⟩

@[expose] def boolReader : Option {b : Bool // b = true} :=
  match h : gate with
  | false => none
  | true => some ⟨gate,h⟩

@[expose] noncomputable def multiple : Option {n : Nat // n = 7} :=
  @Option.rec Nat (fun result => (query = result) → (query = result) → Option {n : Nat // n = 7})
    (fun _ _ => none)
    (fun n h k => some ⟨n,(query_value h).trans ((query_value k).symm.trans (query_value k))⟩)
    query rfl rfl

@[expose] noncomputable def proofFunction : Option Nat :=
  @Option.rec Nat
    (fun result => ((input = result) → Nat) → (input = result) → Option Nat)
    (fun f h => some (f h))
    (fun _ f h => some (f h))
    input (fun _ => 7) rfl

@[expose] noncomputable def continuedFunction : Option Nat :=
  @Option.rec Nat
    (fun result => (input = result) → ((input = result) → Nat) → Option Nat)
    (fun h f => some (f h))
    (fun _ h f => some (f h))
    input rfl (fun _ => 29)

@[expose] noncomputable def dependentData : Option {n : Nat // n = 7} :=
  @Option.rec Nat (fun result => (input = result) → Fin (result.getD 0) → Option {n : Nat // n = 7})
    (fun _ _ => none)
    (fun n h _ => some ⟨n,input_value h⟩)
    input rfl ⟨0,by simp [input,gate_eq]⟩

@[expose] noncomputable def dependentFunction : Option Nat :=
  @Option.rec Nat
    (fun result => ((input = result) → Fin (result.getD 0)) → (input = result) → Option Nat)
    (fun _ _ => none)
    (fun _ f h => some (f h).val)
    input (fun _ => ⟨0,by simp [input,gate_eq]⟩) rfl

end Hex.RCF.DependentQuote
