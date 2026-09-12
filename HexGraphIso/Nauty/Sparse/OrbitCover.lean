/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Orbits
public import HexGraphIso.Nauty.Sparse.FilterCover
public import HexGraphIso.Nauty.Sparse.Pairs
public import HexGraphIso.Nauty.Sparse.PathState
import all HexGraphIso.Nauty.Sparse.Orbits
import all HexGraphIso.Nauty.Sparse.Trace
import all HexGraphIso.Nauty.Invariant.Orbits
import all HexGraphIso.Nauty.Policy.Colors
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- With an empty individualized path, native automorphism soundness
already gives stabilization of the current refined partition. This seeds
the root orbit argument without a generator-stabilization premise. -/
theorem PathInv.empty_trace {G : GraphIso.Sparse.Colored n k} {level : Nat} {st : State n}
    (h : PathInv G level st) (ht : TraceOk G st) (hn : 0 < n) (he : st.fixedpts = VSet.empty) :
    ∀ gamma ∈ st.genTrace, CellStab st.ptn level st.lab gamma := by
  intro gamma hg
  have ha := ht gamma hg
  apply h.stab gamma ha.checked (ha.colors hn)
  intro v _ hv
  change st.fixedpts.mem v = true at hv
  rw [he] at hv
  simp at hv

/-- The actual orbit pointer has a checked word carrier in any frozen
partition stabilized by the accumulated trace. A skipped pointer has a
strictly smaller endpoint, as required by ranked child coverage. -/
theorem OrbitTrace.carrier {G : GraphIso.Sparse.Colored n k}
    {level numcells tv : Nat} {base st : State n}
    (h : OrbitTrace G st) (ht : TraceOk G st) (hb : Ready G level numcells base)
    (hn : 0 < n) (hl : 1 ≤ level) (hv : tv < n)
    (hs : ∀ gamma ∈ st.genTrace, CellStab base.ptn level base.lab gamma)
    (hne : st.orbits[tv]! ≠ tv) :
    ∃ gamma, checkAutom (Graph.context G.graph).g gamma = true ∧
      CellStab base.ptn level base.lab gamma ∧
      gamma[tv]! = st.orbits[tv]! ∧ st.orbits[tv]! < tv := by
  have ho := h ht
  obtain ⟨_, word, hword, he⟩ := orbConn_of_ptr ho hv
  obtain ⟨ha, hstab, hmap⟩ := wordPerm_spec
    (labOk_of_reach hb.ok.labSize hb.ok.reach) hb.ok.ptnSize hb.ok.labSize
    (searchOk_end hn hb.ok hl)
    (fun gamma hg => (ht gamma (by simpa using hg)).checked)
    (fun gamma hg => hs gamma (by simpa using hg)) word hword
  have hle := (ho.2 tv hv).1
  exact ⟨wordPerm n word, ha, hstab, (hmap tv hv).trans he, by omega⟩

/-- The literal first-path orbit guard removes only a child represented
by a strictly smaller child with the same whole sparse subtree maximum.
The frozen-ancestor trace invariant supplies stabilization at this level. -/
theorem CellCover.orbit_skip {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells tc len tv : Nat} {cs : List Nat}
    {base st : State n} {live : Nat → Prop} {best : Option (Key n)} {first : Bool}
    (h : CellCover G.graph tcLevel fuel level numcells tc len cs base live best)
    (hb : Ready G level numcells base) (ho : OrbitTrace G st) (ht : TraceOk G st)
    (hn : 0 < n) (hl : 1 ≤ level) (hc : IsCell base.ptn level tc len)
    (hlen : 1 < len) (hr : tc + len ≤ n) (hf : n < fuel + (numcells + 1))
    (hv : (windowSet n base.lab tc len).mem tv = true)
    (hle : ∀ v, live v → tv ≤ v)
    (hs : ∀ gamma ∈ st.genTrace, CellStab base.ptn level base.lab gamma)
    (hskip : (!first || st.orbits[tv]! == tv) = false) :
    CellCover G.graph tcLevel fuel level numcells tc len cs base (fun v => live v ∧ tv < v) best := by
  have hne : st.orbits[tv]! ≠ tv := by
    cases first
    · simp at hskip
    · simpa using hskip
  obtain ⟨gamma, ha, hstab, hmap, hlt⟩ := ho.carrier ht hb hn hl (windowSet_lt hv) hs hne
  have hsize : base.lab.size = n := hb.ok.labSize
  have hw := windowSet_carry hstab hc (by rw [hsize]; exact hr)
    (labOk_of_reach hb.ok.labSize hb.ok.reach) hv
  apply h.skip hle hw (by rw [hmap]; exact hlt)
  exact hb.vertex_key hn hl ha hstab hc hlen hr hv hf tcLevel

/-- The root's empty path discharges the trace-stabilization requirement
of the actual orbit skip using only native generator soundness. -/
theorem CellCover.empty_orbit {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells tc len tv : Nat} {cs : List Nat}
    {st : State n} {live : Nat → Prop} {best : Option (Key n)} {first : Bool}
    (h : CellCover G.graph tcLevel fuel level numcells tc len cs st live best)
    (hb : Ready G level numcells st) (hp : PathInv G level st)
    (ho : OrbitTrace G st) (ht : TraceOk G st) (hempty : st.fixedpts = VSet.empty)
    (hn : 0 < n) (hl : 1 ≤ level) (hc : IsCell st.ptn level tc len)
    (hlen : 1 < len) (hr : tc + len ≤ n) (hf : n < fuel + (numcells + 1))
    (hv : (windowSet n st.lab tc len).mem tv = true) (hle : ∀ v, live v → tv ≤ v)
    (hskip : (!first || st.orbits[tv]! == tv) = false) :
    CellCover G.graph tcLevel fuel level numcells tc len cs st (fun v => live v ∧ tv < v) best :=
  h.orbit_skip hb ho ht hn hl hc hlen hr hf hv hle (hp.empty_trace ht hn hempty) hskip

end Hex.GraphIso.Nauty.Sparse
