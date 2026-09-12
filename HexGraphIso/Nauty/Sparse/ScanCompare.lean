/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.TouchCompare
public import HexGraphIso.Nauty.Sparse.RowsTransport

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Injective vertex renaming preserves every observed multiplicity. -/
theorem count_map (σ : Renaming n) (seen : List Nat) (v : Nat) :
    (seen.map σ.toFun).count (σ v) = seen.count v := by
  induction seen with
  | nil => rfl
  | cons w ws ih =>
    have he : (σ w == σ v) = (w == v) := Bool.eq_iff_iff.mpr (by
      simp only [beq_iff_eq]
      exact ⟨σ.inj w v, congrArg σ.toFun⟩)
    simp only [List.map_cons, List.count_cons, he, ih]

/-- Exact native counts and sorted first-touch lists transport from the
observed neighbour multiset. Retained counts outside touched cells are
unrestricted and need not agree. -/
theorem CountScan.equiv (σ : Renaming n)
    (hs : CountScan n stamp before marks touched starts hits seen)
    (ht : CountScan n next old final visits other keys observed)
    (ho : touched.toList.Pairwise (· ≤ ·)) (ho' : visits.toList.Pairwise (· ≤ ·))
    (hb : ∀ v ∈ seen, v < n)
    (hkeys : ∀ v, v < n → other[σ v]! = starts[v]!)
    (hp : observed.Perm (seen.map σ.toFun)) :
    touched = visits ∧ ∀ v, v < n → starts[v]! ∈ touched.toList → keys[σ v]! = hits[v]! := by
  have hmap : (observed.map fun v => other[v]!).Perm (seen.map fun v => starts[v]!) := by
    apply (hp.map (fun v => other[v]!)).trans
    rw [List.map_map]
    apply List.Perm.of_eq
    apply List.map_congr_left
    intro v hv
    exact hkeys v (hb v hv)
  refine ⟨hs.touch.eq_of_order ht.touch ho ho' hmap.symm, ?_⟩
  intro v hv hm
  have hc := (hs.touch.members _).mp hm
  rw [ht.counts.get (σ v) ((σ.maps v).mp hv) (by rw [hkeys v hv]; exact hc.1)
    (by rw [hkeys v hv]; exact hmap.mem_iff.mpr hc.2),
    hs.counts.get v hv hc.1 hc.2, hp.count_eq, count_map]

end Hex.GraphIso.Nauty.Sparse
