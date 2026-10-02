/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.OrbitReplay
public import HexGraphIso.Nauty.Sparse.GenerationTrace
import all HexGraphIso.Nauty.Sparse.OrbitReplay
import all HexGraphIso.Nauty.Sparse.GenerationTrace
import all HexGraphIso.Nauty.Invariant.OrbitComplete
import all HexGraphIso.Nauty.Policy.Generated.Trace
import all HexGraphIso.Generated
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

namespace OrbitReplay

variable {G : GraphIso.Sparse.Colored n k} {st out : State n}

/-- Intermediate native joins already store roots at every vertex. -/
theorem flat (h : OrbitReplay st) (ht : TraceOk G st) : Orbit.Flat st.orbits n := by
  rw [h.orbits]
  apply Orbit.flat_fold _ (fun gamma hg => (ht gamma (Array.mem_toList_iff.mp hg)).bound)
  · exact .ofSound (orbSound_orbConn_init [])
  · intro v hv
    have he : (Array.ofFn (n := n) Fin.val)[v]! = v := by
      rw [getElem!_pos _ _ (by simpa using hv), Array.getElem_ofFn]
    simp only [he]

/-- Every emitted generator edge has been joined in the current array,
including admissions that left the orbit count unchanged. -/
theorem trace (h : OrbitReplay st) (ht : TraceOk G st) {gamma : Array Nat}
    (hg : gamma ∈ st.genTrace) {i : Nat} (hi : i < n) :
    st.orbits[gamma[i]!]! = st.orbits[i]! := by
  have hs : Orbit.Stable st.orbits n (fun v => st.orbits[v]!) := h.flat ht
  rw [h.orbits] at hs ⊢
  exact (Orbit.stable_fold _
    (fun gamma hg => (ht gamma (Array.mem_toList_iff.mp hg)).bound) _
    (.ofSound (orbSound_orbConn_init [])) hs).2 gamma (Array.mem_toList_iff.mpr hg) i hi

/-- Words in the generators emitted so far preserve current native
representatives. This applies before the search has completed. -/
theorem generated (h : OrbitReplay st) (ht : TraceOk G st) {p : Perm n}
    (hp : Perm.Generated st.generators p) (v : Fin n) :
    st.orbits[(p.get v).val]! = st.orbits[v.val]! := by
  have he : ∀ v : Fin n, st.orbits[(p.get v).val]! = st.orbits[v.val]! := by
    apply hp.induction
    · intro v; simp
    · intro q hq v
      obtain ⟨gamma, hg, hparse⟩ := List.mem_filterMap.mp hq
      rw [Perm.val_get_of_ofNatArray? hparse]
      exact h.trace ht (Array.mem_toList_iff.mp hg) v.isLt
    · intro p q hp hq v
      rw [Perm.get_comp, hp, hq]
    · intro p hp v
      simpa using (hp (p.inv.get v)).symm
  exact he v

/-- Later joins preserve every connection already represented by an
earlier pointer, provided the executed trace only grows. -/
theorem stable (h : OrbitReplay out) (ht : TraceOk G out)
    (hs : OrbSound (OrbConn st.genTrace.toList n) st.orbits n)
    (hsub : ∀ gamma ∈ st.genTrace, gamma ∈ out.genTrace) :
    Orbit.Stable st.orbits n (fun v => out.orbits[v]!) := by
  intro v hv
  obtain ⟨_, w, hw, he⟩ := orbConn_of_ptr hs hv
  have hr : Generation.Realizes G out.generators w := (Generation.realized ht).mono
    (fun gamma hg => Array.mem_toList_iff.mpr (hsub gamma (Array.mem_toList_iff.mp (hw gamma hg))))
  obtain ⟨p, hp, _, hpv⟩ := hr.word w
  have hh := h.generated ht hp ⟨v, hv⟩
  rw [hpv, he] at hh
  exact hh

end OrbitReplay

/-- Extending the literal emitted array trace extends its decoded
generator list without another automorphism check or graph traversal. -/
theorem State.generators_mono {st out : State n}
    (h : ∀ gamma ∈ st.genTrace, gamma ∈ out.genTrace) :
    ∀ p ∈ st.generators, p ∈ out.generators := by
  intro p hp
  obtain ⟨gamma, hg, he⟩ := List.mem_filterMap.mp hp
  exact List.mem_filterMap.mpr ⟨gamma,
    Array.mem_toList_iff.mpr (h gamma (Array.mem_toList_iff.mp hg)), he⟩

end Hex.GraphIso.Nauty.Sparse
