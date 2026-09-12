/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.TraceContains
public import HexGraphIso.Nauty.Sparse.GenerationFrame
public import HexGraphIso.Nauty.Policy.Generated.Trace
public import HexGraphIso.Nauty.Sparse.Orbits
import all HexGraphIso.Nauty.Sparse.Trace
import all HexGraphIso.Nauty.Sparse.Orbits
import all HexGraphIso.Nauty.Policy.Generated.Trace
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Decode the complete emitted native trace as forward permutations.
Sound reached traces lose no entry; decoding retains order and duplicates
and does not repeat any graph search or adjacency test. -/
@[expose] def State.generators (st : State n) : List (Perm n) :=
  st.genTrace.toList.filterMap (Perm.ofNatArray? n)

/-- Every decoded permutation is exactly its emitted array and preserves
the native graph and ordered colours. -/
theorem TraceOk.generator {G : GraphIso.Sparse.Colored n k} {st : State n}
    (h : TraceOk G st) {p : Perm n} (hp : p ∈ st.generators) : GraphIso.Sparse.IsIso G G p := by
  obtain ⟨gamma, hm, he⟩ := List.mem_filterMap.mp hp
  obtain ⟨hs, q, hq, hv⟩ := h gamma (Array.mem_toList_iff.mp hm)
  have hq' : Perm.ofNatArray? n gamma = some q := Perm.ofNatArray?_eq hs (fun v => (hv v).symm)
  have hsame : p = q := Option.some.inj (he.symm.trans hq')
  exact hsame.symm ▸ hq

namespace Generation

/-- The shared abstract generated-group relation is applied to the
native sparse graph's semantic interpretation. It executes no dense search. -/
abbrev Realizes (G : GraphIso.Sparse.Colored n k) (gs : List (Perm n)) (store : List (Array Nat)) : Prop :=
  Nauty.Generation.Realizes G.toDense gs store

/-- A sound native trace realizes its own complete decoded generator
list. Every emitted array parses successfully, including order zero. -/
theorem realized {G : GraphIso.Sparse.Colored n k} {st : State n} (h : TraceOk G st) :
    Realizes G st.generators st.genTrace.toList := by
  intro gamma hm
  obtain ⟨hs, p, hp, hv⟩ := h gamma (Array.mem_toList_iff.mp hm)
  have he : Perm.ofNatArray? n gamma = some p := Perm.ofNatArray?_eq hs (fun v => (hv v).symm)
  exact ⟨p, .mem (List.mem_filterMap.mpr ⟨gamma, hm, he⟩),
    (GraphIso.Sparse.isIso_toDense G G p).mpr hp, fun v => (hv v).symm⟩

/-- Native orbit pointers are realized by words in a containing trace
whenever those recorded generators fix the active base. -/
theorem pointer {G : GraphIso.Sparse.Colored n k} {st : State n} {gs : List (Perm n)}
    {base : List (Fin n)} (h : OrbitTrace G st) (ht : TraceOk G st)
    (hr : Realizes G gs st.genTrace.toList)
    (hfix : ∀ gamma ∈ st.genTrace, ∀ b ∈ base, gamma[b.val]! = b.val) (v : Fin n) :
    ∃ u : Fin n, u.val = st.orbits[v.val]! ∧ u.val ≤ v.val ∧
      ∃ p, Perm.Generated gs p ∧ GraphIso.Sparse.IsIso G G p ∧ Perm.Fixes base p ∧ p.get v = u := by
  obtain ⟨u, hu, hle, p, hp, hi, hf, he⟩ := Nauty.Generation.carries_pointer (v := v)
    (h ht) hr (fun gamma hm => hfix gamma (Array.mem_toList_iff.mp hm))
  exact ⟨u, hu, hle, p, hp, (GraphIso.Sparse.isIso_toDense G G p).mp hi, hf, he⟩

/-- The public production trace is represented without losing an
emitted generator; this supplies the containing group for the first-path
generation induction. Completeness of that group is a separate theorem. -/
theorem root (G : GraphIso.Sparse.Colored n k) :
    Realizes G (runColored G).generators (runColored G).genTrace.toList :=
  realized (runColored_trace G)

end Generation
end Hex.GraphIso.Nauty.Sparse
