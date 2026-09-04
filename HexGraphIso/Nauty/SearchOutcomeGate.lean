/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeCarry
import all HexGraphIso.Nauty.Search

public section

/-!
The negative-comparison arms of an internal off-path node.

When the refined code is already below the incumbent's, `othernode`
either prunes at once (the first-path agreement is broken) or descends
through the first path's own target cell looking for automorphisms.  The
subtree is dominated in both cases, so its exact maximum is the unchanged
incumbent; what remains is the executable state bookkeeping.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-! # Frame equations of the frozen-downward arm -/

private theorem pushAuto_genTrace'' (st : SearchSt) (pair : Nat × Nat) :
    (pushAuto st pair).genTrace = st.genTrace := by
  rw [pushAuto]
  split <;> rfl

private theorem pushAuto_orbits'' (st : SearchSt) (pair : Nat × Nat) :
    (pushAuto st pair).orbits = st.orbits := by
  rw [pushAuto]
  split <;> rfl

private theorem pushAuto_gcaCanon'' (st : SearchSt) (pair : Nat × Nat) :
    (pushAuto st pair).gcaCanon = st.gcaCanon := by
  rw [pushAuto]
  split <;> rfl

/-- The frozen-downward arm records no generator. -/
theorem processnode_fast_genTrace {ctx : Ctx} {level numcells : Nat}
    {st : SearchSt} (hg : st.eqlevFirst ≠ level ∧ st.compCanon < 0) :
    (processnode ctx level numcells st).2.genTrace = st.genTrace := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt => x.2.genTrace),
    pushAuto_genTrace'', ite_self]
  rw [ite_eq_left hg]

/-- The frozen-downward arm leaves the orbit array alone. -/
theorem processnode_fast_orbits {ctx : Ctx} {level numcells : Nat}
    {st : SearchSt} (hg : st.eqlevFirst ≠ level ∧ st.compCanon < 0) :
    (processnode ctx level numcells st).2.orbits = st.orbits := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt => x.2.orbits),
    pushAuto_orbits'', ite_self]
  rw [ite_eq_left hg]

/-- The frozen-downward arm leaves the canonical guide alone. -/
theorem processnode_fast_gcaCanon {ctx : Ctx} {level numcells : Nat}
    {st : SearchSt} (hg : st.eqlevFirst ≠ level ∧ st.compCanon < 0) :
    (processnode ctx level numcells st).2.gcaCanon = st.gcaCanon := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt => x.2.gcaCanon),
    pushAuto_gcaCanon'', ite_self]
  rw [ite_eq_left hg, ite_eq_right (by decide)]

/-! # State equations of the internal negative branches -/

/-- The prepared state of an off-path node: refinement followed by the
comparison step, before any target selection. -/
theorem otherLeafSt_eq (ctx : Ctx) (level numcells : Nat) (st : SearchSt) :
    otherLeafSt ctx level numcells st =
      otherNodePrep level
        (refine ctx level st.lab st.ptn st.active numcells).longcode
        { st with
          lab := (refine ctx level st.lab st.ptn st.active numcells).lab
          ptn := (refine ctx level st.lab st.ptn st.active numcells).ptn
          active := (refine ctx level st.lab st.ptn st.active numcells).active
          numnodes := st.numnodes + 1 } := rfl

/-- With the first-path agreement broken under a negative comparison,
an internal node prunes at once and returns the leaf event's result. -/
theorem otherNode_gate_state (ctx : Ctx)
    (inf tcLevel fuel level numcells : Nat) (st : SearchSt)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells < ctx.n)
    (hgate : (otherLeafSt ctx level numcells st).eqlevFirst ≠ level ∧
      (otherLeafSt ctx level numcells st).compCanon < 0)
    (hearly : (processnode ctx level
      (refine ctx level st.lab st.ptn st.active numcells).numcells
      (otherLeafSt ctx level numcells st)).1 < Int.ofNat level) :
    otherNode ctx inf tcLevel (fuel + 1) level numcells st =
      processnode ctx level
        (refine ctx level st.lab st.ptn st.active numcells).numcells
        (otherLeafSt ctx level numcells st) := by
  dsimp only [otherLeafSt] at hgate hearly ⊢
  rw [otherNode]
  simp only [hnum, true_and]
  rw [ite_eq_right (by
    intro h
    rcases h with h | h
    · exact hgate.1 (beq_iff_eq.mp h)
    · exact absurd hgate.2 (Int.not_lt.mpr h))]
  rw [ite_eq_left hearly]
  rfl

/-- A negative comparison whose hinted target disagrees with the first
path demotes the agreement depth and prunes at once. -/
theorem otherNode_hintFail_state (ctx : Ctx)
    (inf tcLevel fuel level numcells : Nat) (st : SearchSt)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells < ctx.n)
    (heq : ((otherLeafSt ctx level numcells st).eqlevFirst == level) = true)
    (hneg : (otherLeafSt ctx level numcells st).compCanon < 0)
    (hmis : Int.ofNat (maketargetcell ctx (otherLeafSt ctx level numcells st).lab
        (otherLeafSt ctx level numcells st).ptn level tcLevel
        (otherLeafSt ctx level numcells st).firsttc[level]!).1 ≠
      (otherLeafSt ctx level numcells st).firsttc[level]!)
    (hearly : (processnode ctx level
      (refine ctx level st.lab st.ptn st.active numcells).numcells
      { otherLeafSt ctx level numcells st with
        tctotal := (otherLeafSt ctx level numcells st).tctotal +
          (maketargetcell ctx (otherLeafSt ctx level numcells st).lab
            (otherLeafSt ctx level numcells st).ptn level tcLevel
            (otherLeafSt ctx level numcells st).firsttc[level]!).2.2
        eqlevFirst := level - 1 }).1 < Int.ofNat level) :
    otherNode ctx inf tcLevel (fuel + 1) level numcells st =
      processnode ctx level
        (refine ctx level st.lab st.ptn st.active numcells).numcells
        { otherLeafSt ctx level numcells st with
          tctotal := (otherLeafSt ctx level numcells st).tctotal +
            (maketargetcell ctx (otherLeafSt ctx level numcells st).lab
              (otherLeafSt ctx level numcells st).ptn level tcLevel
              (otherLeafSt ctx level numcells st).firsttc[level]!).2.2
          eqlevFirst := level - 1 } := by
  dsimp only [otherLeafSt] at heq hneg hmis hearly ⊢
  rw [otherNode]
  simp only [hnum, true_and, heq, true_or, ite_true, hneg, ne_eq,
    not_false_eq_true, ite_true, hmis]
  rw [ite_eq_left hearly]
  rfl

/-- A negative comparison whose hinted target agrees with the first path
enters its child loop over that target cell with the comparison still
frozen. -/
theorem otherNode_hint_state (ctx : Ctx)
    (inf tcLevel fuel level numcells : Nat) (st : SearchSt)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells < ctx.n)
    (heq : ((otherLeafSt ctx level numcells st).eqlevFirst == level) = true)
    (hneg : (otherLeafSt ctx level numcells st).compCanon < 0)
    (hmatch : Int.ofNat (maketargetcell ctx
        (otherLeafSt ctx level numcells st).lab
        (otherLeafSt ctx level numcells st).ptn level tcLevel
        (otherLeafSt ctx level numcells st).firsttc[level]!).1 =
      (otherLeafSt ctx level numcells st).firsttc[level]!)
    (hshort : SearchSt.needshortprune (processnode ctx level
      (refine ctx level st.lab st.ptn st.active numcells).numcells
      { otherLeafSt ctx level numcells st with
        tctotal := (otherLeafSt ctx level numcells st).tctotal +
          (maketargetcell ctx (otherLeafSt ctx level numcells st).lab
            (otherLeafSt ctx level numcells st).ptn level tcLevel
            (otherLeafSt ctx level numcells st).firsttc[level]!).2.2 }).2 =
      false) :
    let pre := otherLeafSt ctx level numcells st
    let mt := maketargetcell ctx pre.lab pre.ptn level tcLevel
      pre.firsttc[level]!
    let base := { pre with tctotal := pre.tctotal + mt.2.2 }
    let pr := processnode ctx level
      (refine ctx level st.lab st.ptn st.active numcells).numcells base
    let start := if ¬ cheapautom pr.2.ptn level ctx.n then
      { pr.2 with noncheaplevel := level + 1 } else pr.2
    let L := otherChildLoop ctx inf tcLevel fuel (ctx.n + 1) level
      (refine ctx level st.lab st.ptn st.active numcells).numcells mt.1
      ((nextElem mt.2.1 none).getD 0) (nextElem mt.2.1 none) mt.2.1 start
    otherNode ctx inf tcLevel (fuel + 1) level numcells st =
      if pr.1 < Int.ofNat level then pr
      else match L.1 with
        | some rtn => (rtn, L.2)
        | none => (Int.ofNat level - 1, L.2) := by
  dsimp only
  dsimp only [otherLeafSt] at heq hneg hmatch hshort ⊢
  have hnot : ¬ (Int.ofNat (maketargetcell ctx
      (otherNodePrep level
        (refine ctx level st.lab st.ptn st.active numcells).longcode
        { st with
          lab := (refine ctx level st.lab st.ptn st.active numcells).lab
          ptn := (refine ctx level st.lab st.ptn st.active numcells).ptn
          active := (refine ctx level st.lab st.ptn st.active numcells).active
          numnodes := st.numnodes + 1 }).lab
      (otherNodePrep level
        (refine ctx level st.lab st.ptn st.active numcells).longcode
        { st with
          lab := (refine ctx level st.lab st.ptn st.active numcells).lab
          ptn := (refine ctx level st.lab st.ptn st.active numcells).ptn
          active := (refine ctx level st.lab st.ptn st.active numcells).active
          numnodes := st.numnodes + 1 }).ptn level tcLevel
      (otherNodePrep level
        (refine ctx level st.lab st.ptn st.active numcells).longcode
        { st with
          lab := (refine ctx level st.lab st.ptn st.active numcells).lab
          ptn := (refine ctx level st.lab st.ptn st.active numcells).ptn
          active := (refine ctx level st.lab st.ptn st.active numcells).active
          numnodes := st.numnodes + 1 }).firsttc[level]!).1 ≠
      (otherNodePrep level
        (refine ctx level st.lab st.ptn st.active numcells).longcode
        { st with
          lab := (refine ctx level st.lab st.ptn st.active numcells).lab
          ptn := (refine ctx level st.lab st.ptn st.active numcells).ptn
          active := (refine ctx level st.lab st.ptn st.active numcells).active
          numnodes := st.numnodes + 1 }).firsttc[level]!) :=
    fun h => h hmatch
  simp only [Int.ofNat_eq_natCast] at hnot
  rw [otherNode]
  simp only [hnum, true_and, heq, true_or, ite_true, hneg,
    Int.ofNat_eq_natCast, ite_eq_right hnot, hshort, Bool.false_eq_true,
    ite_false, Int.toNat_natCast]
  generalize hpr : processnode ctx level
    (refine ctx level st.lab st.ptn st.active numcells).numcells _ = pr
  rcases hc : cheapautom pr.2.ptn level ctx.n with _ | _ <;>
    simp only [hc, Bool.false_eq_true, not_false_eq_true, ite_true,
      not_true_eq_false, ite_false] <;>
    generalize hL : (otherChildLoop ctx inf tcLevel fuel (ctx.n + 1)
      level _ _ _ _ _ _) = L <;>
    rcases L with ⟨r, out⟩ <;>
    cases r <;> simp only [Id.run_pure, apply_ite Id.run] <;> rfl

end Hex.GraphIso.Nauty
