/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountResult

public section

namespace Hex.GraphIso.Nauty.Sparse.CountTrace

/-- Uniformity depends on the cell's count multiset, including when its
first vertex changes under a permutation. -/
theorem uniform_iff (lab out hits keys : Array Nat) (hf : first < last)
    (hp : ((segN lab first (last - first)).map fun v => hits[v]!).Perm
      ((segN out first (last - first)).map fun v => keys[v]!)) :
    (∀ q, first ≤ q → q < last → hits[lab[q]!]! = hits[lab[first]!]!) ↔
      (∀ q, first ≤ q → q < last → keys[out[q]!]! = keys[out[first]!]!) := by
  have transport (lab out hits keys : Array Nat)
      (hp : ((segN lab first (last - first)).map fun v => hits[v]!).Perm
        ((segN out first (last - first)).map fun v => keys[v]!))
      (hu : ∀ q, first ≤ q → q < last → hits[lab[q]!]! = hits[lab[first]!]!) :
      ∀ q, first ≤ q → q < last → keys[out[q]!]! = hits[lab[first]!]! := by
    intro q hq he
    have hmem : keys[out[q]!]! ∈ (segN out first (last - first)).map (fun v => keys[v]!) :=
      List.mem_map.mpr ⟨out[q]!, mem_segN_iff.mpr ⟨q - first, by omega, by
        rw [show first + (q - first) = q by omega]⟩, rfl⟩
    obtain ⟨v, hv, hkey⟩ := List.mem_map.mp (hp.mem_iff.mpr hmem)
    obtain ⟨i, hi, rfl⟩ := mem_segN_iff.mp hv
    exact hkey.symm.trans (hu (first + i) (by omega) (by omega))
  constructor
  · intro hu q hq he
    rw [transport lab out hits keys hp hu q hq he,
      transport lab out hits keys hp hu first (Nat.le_refl _) hf]
  · intro hu q hq he
    rw [transport out lab keys hits hp.symm hu q hq he,
      transport out lab keys hits hp.symm hu first (Nat.le_refl _) hf]

/-- Equal ordered counts and initial control determine the complete
split trace's final hash, active set and ordered queue. -/
theorem Result.control_eq {s t : RefineSt n}
    (hs : Result distance first last s lab c) (ht : Result distance first last t out d)
    (hc : control s = control t)
    (hu : (∀ q, first ≤ q → q < last → s.hits[s.lab[q]!]! = s.hits[s.lab[first]!]!) ↔
      (∀ q, first ≤ q → q < last → t.hits[t.lab[q]!]! = t.hits[t.lab[first]!]!))
    (hk : ∀ q, first ≤ q → q < last → s.hits[lab[q]!]! = t.hits[out[q]!]!) : c = d := by
  cases hs with
  | uniform hs =>
    cases ht with
    | uniform ht => rw [hc]
    | divided hn hm hv ht =>
      obtain ⟨q, hq, he, hne⟩ := hn
      exact False.elim (hne (hu.mp hs q hq he))
  | divided hn hm hv hs =>
    cases ht with
    | uniform ht =>
      obtain ⟨q, hq, he, hne⟩ := hn
      exact False.elim (hne (hu.mpr ht q hq he))
    | divided hn' hm' hv' ht =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hm.unique hm' hv hv' hk
      split at hs
      · rename_i he
        simp only [he, ite_true] at ht
        rw [hs, ht, hc, he]
      · rename_i he
        simp only [he, ite_false] at ht
        dsimp only at hs ht
        have bounds := hm.bounds
        have htrace := hs.congr (fun q hq hlast => hk q (by omega) hlast)
        exact htrace.deterministic (by simpa only [hc] using ht)

end Hex.GraphIso.Nauty.Sparse.CountTrace
