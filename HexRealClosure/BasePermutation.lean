/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.BasePresentation
public import Init.Data.List.FinRange

public section

namespace Hex.RealClosure.BaseContext.BaseTower

private def word (source : List ConstantKey) : List ConstantKey → Nat → Option (List Nat)
  | [], _ => if source.isEmpty then some [] else none
  | key :: target, offset => do
    let index ← source.findIdx? (fun previous => previous == key)
    let later ← word (source.erase key) target (offset + 1)
    pure ((List.range index).reverse.map (fun i => offset + i) ++ later)

/-- Apply a finite sequence of adjacent exchanges, checking every position. -/
def exchange? (n : Nat) : List Nat → Option (FieldEmbedding (BaseTower n) (BaseTower n))
  | [] => some (FieldEmbedding.identity (BaseTower n))
  | i :: rest =>
    if bound : i + 1 < n then
      (exchange? n rest).map (fun later => (adjacent n i bound).comp later)
    else none

/-- Check the image of every provider variable against its exact registry key.
Lists are stored in predecessor order; variables are counted from outside. -/
@[expose] def bindings (source target : List ConstantKey)
    (embedding : FieldEmbedding (BaseTower source.length) (BaseTower target.length)) : Bool :=
  (List.finRange source.length).all fun i =>
    (List.finRange target.length).any fun j =>
      decide (source.reverse[i] = target.reverse[j]) &&
        decide (embedding.value (generator source.length i i.isLt) =
          generator target.length j j.isLt)

/-- A checked inclusion of fields identified by provider keys, with potentially
different variable orders and additional target variables.
This retains arithmetic embeddings and literal key bindings; order agreement
for actual real providers belongs to their companion models. -/
structure Inclusion (source target : List ConstantKey) where
  private mk ::
  embedding : FieldEmbedding (BaseTower source.length) (BaseTower target.length)
  checked : bindings source target embedding = true

/-- Build a native key-bound embedding using constant inclusions and adjacent
exchanges. No provider is evaluated and no progress proof is rebuilt. -/
def Inclusion.make? (source target : List ConstantKey) : Option (Inclusion source target) := do
  if source.Nodup ∧ target.Nodup then
    if depth : source.length ≤ target.length then
      let extra := target.length - source.length
      let additional := target.reverse.filter (fun key => !(source.contains key))
      let positions ← word (additional ++ source.reverse) target.reverse 0
      let permutation ← exchange? target.length positions
      have total : source.length + extra = target.length := by dsimp [extra]; omega
      let initial : FieldEmbedding (BaseTower source.length) (BaseTower target.length) :=
        total ▸ extend source.length extra
      let embedding := initial.comp permutation
      if checked : bindings source target embedding = true then
        some ⟨embedding, checked⟩
      else none
    else none
  else none

/-- Every accepted source variable has the same exact key in its target slot. -/
theorem Inclusion.binding {source target : List ConstantKey} (permutation : Inclusion source target)
    (i : Fin source.length) :
    ∃ j : Fin target.length, source.reverse[i] = target.reverse[j] ∧
      permutation.embedding.value (generator source.length i i.isLt) =
        generator target.length j j.isLt := by
  have checked := permutation.checked
  rw [bindings] at checked
  have accepted := List.all_eq_true.mp checked i (List.mem_finRange i)
  obtain ⟨j, _, matched⟩ := List.any_eq_true.mp accepted
  have pair := Bool.and_eq_true_iff.mp matched
  exact ⟨j, of_decide_eq_true pair.1, of_decide_eq_true pair.2⟩

end Hex.RealClosure.BaseContext.BaseTower

namespace Hex.RealClosure.BaseContext

/-- Check a key-bound map between actual provider chains, retaining their
original dictionaries, providers and progress proofs. -/
def RealChain.reorder? {registry : Registry} {K L : Type}
    [Lean.Grind.Field K] [DecidableEq K] [Lean.Grind.Field L] [DecidableEq L]
    {sourceApprox : K → Rat → OrderedFn.Oracle.Bounds} {sourceSign : K → Int}
    {targetApprox : L → Rat → OrderedFn.Oracle.Bounds} {targetSign : L → Int}
    (target : RealChain registry L targetApprox targetSign)
    (source : RealChain registry K sourceApprox sourceSign) : Option (FieldEmbedding K L) :=
  (BaseTower.Inclusion.make? source.keys target.keys).map fun permutation =>
    (source.encode.comp permutation.embedding).comp target.decode

end Hex.RealClosure.BaseContext

/-- info: 'Hex.RealClosure.BaseContext.BaseTower.Inclusion.binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.BaseTower.Inclusion.binding
