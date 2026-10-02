/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CompactRun

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Predicate classes transport through a mapped permutation. Predicate
agreement is needed only on the traversed source vertices. -/
theorem filter_transport {seen visits : List Nat} (f : Nat → Nat) (p q : Nat → Bool)
    (hp : visits.Perm (seen.map f)) (hk : ∀ v ∈ seen, q (f v) = p v) :
    (visits.filter q).Perm ((seen.filter p).map f) := by
  have h := hp.filter q
  rw [List.filter_map] at h
  apply h.trans (List.Perm.of_eq ?_)
  apply congrArg (List.map f)
  exact List.filter_congr hk

/-- The executed compaction's cut and collected-hit count depend only on
the transported predicate classes, including either uniform case. -/
theorem Compact.counts_map (f : Nat → Nat)
    (hs : Compact before p first last seen lab hit cut)
    (ht : Compact other q first last visits out collected next)
    (hp : visits.Perm (seen.map f)) (hk : ∀ v ∈ seen, q (f v) = p v) :
    cut = next ∧ hit.size = collected.size := by
  have hkeep := (filter_transport f (fun v => !p v) (fun v => !q v) hp
    (fun v hv => congrArg Bool.not (hk v hv))).length_eq
  have hhit := (filter_transport f p q hp hk).length_eq
  simp only [List.length_map] at hkeep hhit
  have hs' := congrArg List.length hs.hits
  have ht' := congrArg List.length ht.hits
  simp only [Array.length_toList] at hs' ht'
  have hsc := hs.count
  have htc := ht.count
  constructor <;> omega

end Hex.GraphIso.Nauty.Sparse
