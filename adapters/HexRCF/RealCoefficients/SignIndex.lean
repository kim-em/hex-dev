/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.LiteralSign
public section

/-! Index finite sign evidence without changing its authentication. -/

namespace Hex.RCF.RealCoefficients.LiteralSign

namespace Table

variable {D : Type u} [DecidableEq D]

/-- Query the original evidence through an untrusted positional index.
A missing route uses the original linear lookup, preserving every recorded
hit even when the routing tree or comparator is malformed. -/
@[expose] def lookupIndex (table : Table D) (compare : D → D → Ordering)
    (index : Index) (key : D) : Option Int :=
  match index.lookup table.entries.toArray compare key with
  | some value => some value
  | none => table.lookup? key

/-- Indexing cannot lose a hit already recorded in the original table. -/
theorem lookupIndex_isSome (table : Table D) (compare : D → D → Ordering)
    (index : Index) (key : D) (recorded : (table.lookup? key).isSome = true) :
    (table.lookupIndex compare index key).isSome = true := by
  unfold lookupIndex
  cases index.lookup table.entries.toArray compare key with
  | none => exact recorded
  | some value => rfl

theorem lookupIndex_spec (table : Table D) (query : D → Hex.DensePoly Rat)
    (compare : D → D → Ordering) (index : Index) (eval : D → ℝ) (x : ℝ)
    (hx : (realPoly table.head).IsRoot x)
    (hl : (table.lower : ℝ) < x) (hu : x < (table.upper : ℝ))
    (heval : ∀ a, eval a = (realPoly (query a)).eval x)
    (accepted : table.check query = true) (key : D) (value : Int)
    (hit : table.lookupIndex compare index key = some value) :
    value = (SignType.sign (eval key) : Int) := by
  unfold lookupIndex at hit
  cases routed : index.lookup table.entries.toArray compare key with
  | none =>
      exact table.lookup_spec query eval x hx hl hu heval accepted key value
        (by simpa only [routed] using hit)
  | some found =>
      have sameValue : found = value := Option.some.inj (by simpa only [routed] using hit)
      obtain ⟨entry, member, same, valueEq⟩ := index.lookup_entry
        table.entries.toArray compare key found routed
      have actual := table.entry_spec query entry member x hx hl hu accepted
      rw [same, ← heval, valueEq, sameValue] at actual
      exact actual

/-- As with linear lookup, missing entries use the mathematical sign only.
Executable replay must resolve its finite reads from the checked table. -/
@[expose] noncomputable def signIndex (table : Table D) (compare : D → D → Ordering)
    (index : Index) (eval : D → ℝ) (key : D) : Int :=
  match table.lookupIndex compare index key with
  | some value => value
  | none => (SignType.sign (eval key) : Int)

theorem signIndex_spec (table : Table D) (query : D → Hex.DensePoly Rat)
    (compare : D → D → Ordering) (index : Index) (eval : D → ℝ) (x : ℝ)
    (hx : (realPoly table.head).IsRoot x)
    (hl : (table.lower : ℝ) < x) (hu : x < (table.upper : ℝ))
    (heval : ∀ a, eval a = (realPoly (query a)).eval x)
    (accepted : table.check query = true) (key : D) :
    table.signIndex compare index eval key = (SignType.sign (eval key) : Int) := by
  unfold signIndex
  cases hit : table.lookupIndex compare index key with
  | none => rfl
  | some value =>
    exact table.lookupIndex_spec query compare index eval x
      hx hl hu heval accepted key value hit

end Table
end Hex.RCF.RealCoefficients.LiteralSign
