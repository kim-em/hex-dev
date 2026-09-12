/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.OrbitClosure
public import HexGraphIso.Nauty.Policy.Generated.Cover
import all HexGraphIso.Nauty.Sparse.Orbits
import all HexGraphIso.Nauty.Policy.Generated.Cover
import all HexGraphIso.Nauty.Policy.Generated.Trace
import all HexGraphIso.Orbit
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The least vertex of a true stabilizer orbit remains its own native
representative whenever the emitted trace fixes that base. -/
theorem OrbitTrace.root {G : GraphIso.Sparse.Colored n k} {st : State n}
    {base : List (Fin n)} {guide : Fin n} (h : OrbitTrace G st) (ht : TraceOk G st)
    (hfix : ∀ gamma ∈ st.genTrace, ∀ b ∈ base, gamma[b.val]! = b.val)
    (hmin : ∀ v, Aut.Orbit G.toDense base guide v → guide.val ≤ v.val) :
    st.orbits[guide.val]! = guide.val := by
  obtain ⟨u, hu, hle, p, _, hi, hf, he⟩ :=
    Generation.pointer h ht (Generation.realized ht) hfix guide
  have hm := hmin u ⟨p, (GraphIso.Sparse.isIso_toDense G G p).mpr hi, hf, he⟩
  omega

/-- At an advanced cursor, generated coverage and the literal join
invariant make the executed counter test equivalent to membership in
the guide's full point-stabilizer orbit. -/
theorem OrbitReplay.mark {G : GraphIso.Sparse.Colored n k} {st : State n}
    {base : List (Fin n)} {guide tv : Fin n} {cell : VSet n}
    (h : OrbitReplay st) (ht : TraceOk G st) (ho : OrbitTrace G st)
    (hc : Nauty.Generation.Cover G.toDense st.generators base guide cell (some tv.val))
    (hv : cell.mem tv.val = true)
    (hfix : ∀ gamma ∈ st.genTrace, ∀ b ∈ base, gamma[b.val]! = b.val)
    (hmin : ∀ v, Aut.Orbit G.toDense base guide v → guide.val ≤ v.val) :
    st.orbits[tv.val]! = guide.val ↔ Aut.Orbit G.toDense base guide tv := by
  constructor
  · intro he
    obtain ⟨u, hu, _, p, _, hi, hf, hp⟩ :=
      Generation.pointer ho ht (Generation.realized ht) hfix tv
    have hu' : u = guide := Fin.ext (hu.trans he)
    have hh : Aut.Orbit G.toDense base tv guide :=
      ⟨p, (GraphIso.Sparse.isIso_toDense G G p).mpr hi, hf, hp.trans hu'⟩
    exact hh.symm
  · intro horbit
    obtain ⟨p, hp, _, _, he⟩ := hc.past tv horbit hv (by change ¬ tv.val < tv.val; omega)
    have hh := h.generated ht hp tv
    rw [he, ho.root ht hfix hmin] at hh
    exact hh.symm

end Hex.GraphIso.Nauty.Sparse
