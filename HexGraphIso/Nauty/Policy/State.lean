/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Scatter
import all HexGraphIso.Nauty.Search.Engine
import all HexGraphIso.Nauty.Search.Search

public section

/-!
A proof-side view of the flat engine state supplies the existing
comparison and partition lemmas. The permutation scratch is omitted,
and pending short-prune requests belong to the exit rather than this
view. No executable search calls the view.
-/

namespace Hex.GraphIso.Nauty.Engine

variable {n : Nat}

/-- The common search fields, without a pending short-prune request. -/
def Search.view (st : Search n) : SearchSt n :=
  {
    lab := st.lab
    ptn := st.ptn
    active := st.active
    orbits := st.orbits
    fixedpts := st.fixedpts
    autos := st.autos
    wsCap := st.wsCap
    firstcode := st.firstcode
    canoncode := st.canoncode
    firsttc := st.firsttc
    firstlab := st.firstlab
    canonlab := st.canonlab
    canong := st.canong
    samerows := st.samerows
    compCanon := st.compCanon
    eqlevFirst := st.eqlevFirst
    eqlevCanon := st.eqlevCanon
    gcaFirst := st.gcaFirst
    gcaCanon := st.gcaCanon
    canonlevel := st.canonlevel
    noncheaplevel := st.noncheaplevel
    allsamelevel := st.allsamelevel
    cosetindex := st.cosetindex
    stabvertex := st.stabvertex
    numnodes := st.numnodes
    tctotal := st.tctotal
    canupdates := st.canupdates
    numorbits := st.numorbits
    numgenerators := st.numgenerators
    numbadleaves := st.numbadleaves
    maxlevel := st.maxlevel
    genTrace := st.genTrace }

/-- Refinement updates the common partition fields and node counter. -/
theorem view_visit (ctx : Ctx n) (level numcells : Nat) (st : Search n) :
    let r := refine ctx level st.lab st.ptn st.active numcells
    (visit ctx level numcells st).2.2.view =
      { st.view with
        lab := r.lab
        ptn := r.ptn
        active := r.active
        numnodes := st.numnodes + 1 } := by
  rfl

/-- A child's common fields are the breakout result and the fixed vertex. -/
theorem view_child (first : Bool) (level tc tv : Nat) (st : Search n) :
    let br := breakout n st.lab st.ptn (level + 1) tc tv
    let base := { st.view with
      lab := br.1
      ptn := br.2.1
      active := br.2.2
      fixedpts := st.fixedpts.insert tv }
    (child first level tc tv st).view =
      if first then { base with cosetindex := tv } else base := by
  cases first <;> rfl

/-- Scattering changes no common search field. -/
theorem view_scatter (ref : Array Nat) (st : Search n) :
    (scatter ref st).view = st.view := by
  rw [scatter_eq]
  rfl

/-- Workspace insertion commutes with the common state view. -/
theorem view_pushAuto (st : Search n) (pair : VSet n × VSet n) :
    (pushAuto st pair).view = Nauty.pushAuto st.view pair := by
  unfold pushAuto Nauty.pushAuto
  simp only [Search.view]
  split <;> simp_all

/-- The first leaf installs the same comparison and reference fields. -/
theorem view_firstterminal (level : Nat) (st : Search n) :
    (firstterminal level st).view = Nauty.firstterminal level st.view := by
  rfl

/-- Code comparison commutes with the common state view. -/
theorem view_compareCodes (level code : Nat) (st : Search n) :
    (compareCodes level code st).view = otherNodePrep level code st.view := by
  unfold compareCodes otherNodePrep
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Search.view]
  dsimp only [Search.view]
  rfl

/-- The separated partition rescan and clamps implement recovery. -/
theorem view_recover (inf level : Nat) (st : Search n) :
    (recoverLevels level (recoverPtn inf level st)).view =
      Nauty.recover n inf level st.view := by
  unfold recoverLevels recoverPtn Nauty.recover
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite Search.view]
  dsimp only [Search.view]
  rfl

/-- The bounded workspace does not change the full generator trace. -/
theorem pushAuto_trace (st : Search n) (pair : VSet n × VSet n) :
    (pushAuto st pair).genTrace = st.genTrace := by
  rw [pushAuto]
  split <;> rfl

/-- Admission appends the completed scratch permutation to the full trace. -/
theorem admit_trace (st : Search n) :
    (admit st).genTrace = st.genTrace.push st.workperm := by
  simp only [admit, Id.run_pure, pushAuto_trace]

/-- Admitting a checked permutation preserves validity of the full trace. -/
theorem admit_checked {ctx : Ctx n} {st : Search n}
    (htrace : ∀ γ ∈ st.genTrace, checkAutom ctx.g γ = true)
    (hwork : checkAutom ctx.g st.workperm = true) :
    ∀ γ ∈ (admit st).genTrace, checkAutom ctx.g γ = true := by
  intro γ hγ
  rw [admit_trace, Array.mem_push] at hγ
  rcases hγ with hγ | rfl
  · exact htrace γ hγ
  · exact hwork

end Hex.GraphIso.Nauty.Engine
