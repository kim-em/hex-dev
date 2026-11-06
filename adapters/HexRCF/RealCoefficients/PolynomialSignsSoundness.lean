/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.PolynomialSigns
public import HexRCF.RealCoefficients.PolynomialBoundsSoundness
public section

namespace Hex.RCF.RealCoefficients.PolynomialSigns
open Hex.OrderedFn.Oracle PolynomialBounds LiteralSign

/-- An accepted row identifies its exact stored polynomial at the same fixed
valuation. No source field or coefficient zero-reflection law is used. -/
theorem entry_spec (bounds : Fin n → Bounds) (values : Fin n → ℝ)
    (contained : ∀ i, Contains (bounds i) (values i))
    (entries : Array (Entry (Poly n))) (accepted : check bounds entries = true)
    (entry : Entry (Poly n)) (member : entry ∈ entries.toList) :
    entry.value = (SignType.sign (PolynomialBounds.value values entry.key) : Int) := by
  have row := Array.all_eq_true_iff_forall_mem.mp accepted entry
    (Array.mem_toList_iff.mp member)
  have observed := (Bool.and_eq_true_iff.mp row).2
  exact PolynomialBounds.sign_spec bounds values contained entry.key entry.value
    (of_decide_eq_true observed)

/-- Index hits retain exact key/value bindings for arbitrary routing trees.
Missing routes remain missing; finite coverage is checked by the consumer. -/
theorem lookup_spec (bounds : Fin n → Bounds) (values : Fin n → ℝ)
    (contained : ∀ i, Contains (bounds i) (values i))
    (entries : Array (Entry (Poly n))) (accepted : check bounds entries = true)
    (index : Index) (key : Poly n) (value : Int)
    (hit : lookup entries index key = some value) :
    value = (SignType.sign (PolynomialBounds.value values key) : Int) := by
  obtain ⟨entry, member, sameKey, sameValue⟩ :=
    index.lookup_entry entries keyOrder key value hit
  have observed := entry_spec bounds values contained entries accepted entry member
  simpa only [sameKey, sameValue] using observed

end Hex.RCF.RealCoefficients.PolynomialSigns
