/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.GeneratedRoot
public import HexGraphIso.Nauty.Sparse.OrbitClosure
import all HexGraphIso.Nauty.Sparse.GenerationTrace
import all HexGraphIso.Nauty.Sparse.OrbitReplay
import all HexGraphIso.Nauty.Invariant.OrbitComplete
import all HexGraphIso.Generated
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Every pointer stored by the actual sparse search is already a root. -/
theorem orbits_flat (G : GraphIso.Sparse.Colored n k) : Orbit.Flat (runColored G).orbits n :=
  (runColored_orbitReplay G).flat (runColored_trace G)

/-- The final native representatives identify both ends of every emitted
generator edge, including admissions that did not reduce the orbit count. -/
theorem orbits_trace (G : GraphIso.Sparse.Colored n k) {gamma : Array Nat}
    (hg : gamma ∈ (runColored G).genTrace) {i : Nat} (hi : i < n) :
    (runColored G).orbits[gamma[i]!]! = (runColored G).orbits[i]! :=
  (runColored_orbitReplay G).trace (runColored_trace G) hg hi

/-- The actual representatives are invariant under every word in the
actual emitted generator list. -/
theorem orbits_generated {G : GraphIso.Sparse.Colored n k} {p : Perm n}
    (hp : Perm.Generated (runColored G).generators p) (v : Fin n) :
    (runColored G).orbits[(p.get v).val]! = (runColored G).orbits[v.val]! :=
  (runColored_orbitReplay G).generated (runColored_trace G) hp v

/-- Two vertices have the same native output representative exactly when
a colour-preserving automorphism carries one to the other. -/
theorem orbits_eq_iff (G : GraphIso.Sparse.Colored n k) (u v : Fin n) :
    (runColored G).orbits[u.val]! = (runColored G).orbits[v.val]! ↔
      ∃ p, GraphIso.Sparse.IsIso G G p ∧ p.get u = v := by
  constructor
  · intro he
    obtain ⟨p, hp, hu⟩ := orbit_iso G u
    obtain ⟨q, hq, hv⟩ := orbit_iso G v
    refine ⟨q.inv.comp p, hp.trans hq.symm, ?_⟩
    have hh : p.get u = q.get v := Fin.ext (hu.trans (he.trans hv.symm))
    rw [Perm.get_comp, hh, Perm.inv_get_get]
  · rintro ⟨p, hp, rfl⟩
    exact (orbits_generated (runColored_generates G hp) u).symm

/-- The stored representative is the least vertex in the full native
automorphism orbit, not merely the representative of a discovered subgroup. -/
theorem orbit_le (G : GraphIso.Sparse.Colored n k) (u v : Fin n)
    (h : ∃ p, GraphIso.Sparse.IsIso G G p ∧ p.get u = v) :
    (runColored G).orbits[u.val]! ≤ v.val := by
  rw [(orbits_eq_iff G u v).mpr h]
  exact ((runColored_orbits G).2 v.val v.isLt).1

/-- The stored orbit count is exactly the number of least representatives
of the full automorphism orbits. It is the actual `orbjoin` count, with no
postprocessing search or replacement computation. -/
theorem numorbits_eq_count (G : GraphIso.Sparse.Colored n k) :
    (runColored G).numorbits =
      (List.range n).countP (fun i => (runColored G).orbits[i]! == i) := by
  have count_fold : ∀ (xs : List (Array Nat)), (∀ gamma ∈ xs, ∀ i, i < n → gamma[i]! < n) →
      ∀ (o : Array Nat) (count : Nat), Orbit.Descending o n →
      count = (List.range n).countP (fun i => o[i]! == i) →
      (xs.foldl (fun s gamma => orbjoin s.1 gamma n) (o, count)).2 =
        (List.range n).countP (fun i => (xs.foldl (fun s gamma => orbjoin s.1 gamma n) (o, count)).1[i]! == i) := by
    intro xs
    induction xs with
    | nil => intros; assumption
    | cons gamma xs ih =>
      intro hx o count hd hc
      have hg := hx gamma List.mem_cons_self
      exact ih (fun delta hm => hx delta (List.mem_cons_of_mem _ hm)) _ _
        (hd.orbjoin hg) (Orbit.count_orbjoin hd hg)
  have hinit : n = (List.range n).countP (fun i => (Array.ofFn (n := n) Fin.val)[i]! == i) := by
    have he : (List.range n).countP (fun i => (Array.ofFn (n := n) Fin.val)[i]! == i) =
        (List.range n).length := by
      apply List.countP_eq_length.mpr
      intro i hi
      have hb := List.mem_range.mp hi
      rw [getElem!_pos _ _ (by simpa using hb), Array.getElem_ofFn]
      simp
    simpa only [List.length_range] using he.symm
  have hc := count_fold (runColored G).genTrace.toList
    (fun gamma hm => (runColored_trace G gamma (Array.mem_toList_iff.mp hm)).bound)
    (Array.ofFn (n := n) Fin.val) n (.ofSound (orbSound_orbConn_init [])) hinit
  rw [← runColored_orbitReplay G] at hc
  exact hc

end Hex.GraphIso.Nauty.Sparse
