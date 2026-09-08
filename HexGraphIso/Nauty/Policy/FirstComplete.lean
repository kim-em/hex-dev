/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.FirstTail
import all HexGraphIso.Nauty.Policy.FirstTail
import all HexGraphIso.Nauty.Policy.FirstWitness
import all HexGraphIso.Nauty.Policy.FirstBounds
import all HexGraphIso.Nauty.Policy.FirstHistory
import all HexGraphIso.Nauty.Policy.FirstPath
import all HexGraphIso.Nauty.Policy.First
import all HexGraphIso.Nauty.Policy.MaxInit
import all HexGraphIso.Nauty.Policy.MaxEntry
import all HexGraphIso.Nauty.Policy.MaxPrepare
import all HexGraphIso.Nauty.Policy.MaxReturnTrace
import all HexGraphIso.Nauty.Policy.MaxReceive
import all HexGraphIso.Nauty.Policy.MaxResume
import all HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Policy.MaxContract
import all HexGraphIso.Nauty.Policy.Alignment
import all HexGraphIso.Nauty.Policy.Calls
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Search.Search

public section

namespace Hex.GraphIso.Nauty.Engine.Max

variable {n k : Nat}

/-- A first call returns normally to its parent. The induction proves
the guiding child's return and initializes its actual remaining sweep. -/
theorem firstPath_returns {G : Colored n k} {tcLevel fuel level numcells last : Nat}
    {st leaf : Search n}
    (hp : Generic.FirstPath { g := rowsOf G } tcLevel fuel level numcells st last leaf)
    (hn : ∀ f, f < fuel → (contract G tcLevel).nodeValid f
      (Generic.nodeCall { g := rowsOf G } (n + 2) tcLevel f))
    {cs bs fs : List Nat} {parents : Parents n}
    (hi : NodeInput G { g := rowsOf G } tcLevel fuel true ⟨level, numcells, cs, st⟩ bs fs parents) :
    (Engine.node true { g := rowsOf G } (n + 2) tcLevel fuel level numcells st).1 =
      .unwind (level - 1) false := by
  induction hp generalizing cs bs fs parents with
  | leaf fuel level numcells st hdisc =>
    rw [node_first]
    simp only [hdisc, beq_self_eq_true, ↓reduceIte, Id.run_pure]
  | @step fuel level numcells last st leaf tv hopen htv horbit tail ih =>
    let ctx : Ctx n := { g := rowsOf G }
    let r := Generic.prepareFirst ctx tcLevel level numcells st
    let R := st.refined ctx level numcells
    let l : Loop n := ⟨⟨level, numcells, cs, st⟩, true⟩
    let ready := cheapCheck true level r.2.2.2.2
    let ch := child true level r.2.1.toNat tv ready
    let raw := Engine.node true ctx (n + 2) tcLevel fuel (level + 1) (r.1 + 1) ch
    let left := { afterChildFirst level tv raw.2 with fixedpts := raw.2.fixedpts.erase tv }
    let restored := recoverLevels level (recoverPtn (n + 2) level left)
    let parent : Parent n := ⟨l, ready, tv, bs, fs⟩
    have hp : Generic.FirstPath ctx tcLevel (fuel + 1) level numcells st last leaf :=
      .step hopen htv horbit tail
    have htv' : r.2.2.1.nextElem none = some tv := htv
    have hn0 : 0 < n := by have := hi.frame.positive; have := hi.frame.depth; omega
    have hs : SweepInput G ctx tcLevel fuel (n + 1) true level r.1 r.2.1.toNat tv
        (some tv) r.2.2.1 0 ready l bs fs parents := by
      have hh := hi.first_input (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G) hopen
      change SweepInput G ctx tcLevel fuel (n + 1) true level r.1 r.2.1.toNat
        ((r.2.2.1.nextElem none).getD 0) (r.2.2.1.nextElem none) r.2.2.1 0 ready l bs fs parents at hh
      simpa only [htv', Option.getD_some] using hh
    have hc : NodeInput G ctx tcLevel fuel true
        ⟨level + 1, r.1 + 1, l.codes ctx, ch⟩ bs fs (parents.push parent) := by
      have hh := hs.push (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G)
      simpa only [Parent.child, parent, l, ch, Loop.prepare, r, ctx, Generic.prepareFirst,
        policy, Generic.Policy.visit, Generic.Policy.recordFirst, Generic.Policy.chooseTarget,
        Bool.true_and, beq_self_eq_true, ↓reduceIte] using hh
    have hret : raw.1 = .unwind level false := by
      simpa only [raw, ch, ready, r, ctx, policy, Generic.Policy.child, Generic.Policy.cheapCheck, Nat.add_sub_cancel] using ih (fun f hf => hn f (by omega)) hc
    have hcall : Engine.node (true && tv == tv) ctx (n + 2) tcLevel fuel
        (level + 1) (r.1 + 1) (child true level r.2.1.toNat tv ready) =
          (.unwind level false, raw.2) := by
      simp only [Bool.true_and, beq_self_eq_true]
      exact Prod.ext hret rfl
    have hv : (!true || ready.orbits[tv]! == tv) = true := by
      change ready.orbits[tv]! = tv at horbit
      simp only [Bool.not_true, Bool.false_or, beq_iff_eq]
      exact horbit
    obtain ⟨hgen, hanc⟩ := hs.received_generators (hn fuel (Nat.lt_succ_self _)) hcall
    obtain ⟨bs', fs', hs', _, _⟩ := hs.received_input (hn fuel (Nat.lt_succ_self _)) hv hcall hgen hanc
    simp only [Bool.true_and, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true,
      Bool.not_true, Bool.false_and] at hs'
    change SweepInput G ctx tcLevel fuel n true level r.1 r.2.1.toNat tv
      (r.2.2.1.nextElem (some tv)) r.2.2.1
      (if restored.orbits[tv]! == tv then 0 + 1 else 0) restored l bs' fs' parents at hs'
    obtain ⟨targets, key, href, hm⟩ := firstPath_witness hp hn hi
    have hr : restored.reference = (Engine.node true ctx (n + 2) tcLevel
        (fuel + 1) level numcells st).2.reference := by
      have hraw : raw.2.reference = (Engine.node true ctx (n + 2) tcLevel
          (fuel + 1) level numcells st).2.reference :=
        (firstPath_reference tail).trans (firstPath_reference hp).symm
      exact ((referencePolicy ctx (n + 2) tcLevel).recover level left).trans hraw
    have hm' := matches_reference hm hr
    have hf := firstPath_floor (inf := n + 2) tail
    change level + 1 ≤ raw.2.allsamelevel ∧ level + 1 ≤ raw.2.eqlevFirst at hf
    have hsame : level < restored.allsamelevel := by
      rw [recover_same]
      change level < raw.2.allsamelevel
      omega
    have heq : restored.eqlevFirst = level := by
      rw [recover_eqlev]
      change min raw.2.eqlevFirst level = level
      exact Nat.min_eq_right (by omega)
    have hg : restored.gcaFirst = level := (gcaPolicy ctx (n + 2) tcLevel).recover level left
    have hit := refined_iter (ctx := ctx) hn0 hi.frame.positive hi.frame.partition
    have hpast : Generic.Past true tv (r.2.2.1.nextElem (some tv)) := by
      intro _ v hv
      have hh := (VSet.nextElem_eq_some_iff.mp hv).2.1
      change tv + 1 ≤ v at hh
      omega
    have hfields := l.prepare_frame ctx tcLevel
    have hd := hs'.tail_done (hn fuel (Nat.lt_succ_self _)) hpast hit
      hfields.2.1.symm hfields.2.2.symm (show R.numcells = r.1 from rfl)
      href.occurs hm' hg heq hsame
    have hsweep : (Engine.sweep true ctx (n + 2) tcLevel fuel (n + 1) level r.1
        r.2.1.toNat tv (some tv) r.2.2.1 0 ready).1 = .done := by
      have he := (hs.receive_call (hn fuel (Nat.lt_succ_self _)) hv hcall
        (Generic.sweepCall ctx (n + 2) tcLevel fuel n)).1
      unfold Generic.nodeCall Generic.sweepCall at he
      rw [sweep_eq_generic, Generic.sweep, he]
      simp only [← sweep_eq_generic, Bool.true_and, beq_self_eq_true,
        Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      dsimp only [restored, left, afterChildFirst] at hd ⊢
      exact hd
    rw [node_first]
    simp only [beq_eq_false_iff_ne.mpr hopen, Bool.false_eq_true, ↓reduceIte, htv, Option.getD_some]
    rw [hsweep]
    rfl

/-- The complete first-path conclusion uses only smaller maximum and
trace contracts, with no assumed return or reference-covering sweep. -/
theorem firstPath_complete {G : Colored n k} {tcLevel fuel level numcells last : Nat}
    {st leaf : Search n}
    (hp : Generic.FirstPath { g := rowsOf G } tcLevel fuel level numcells st last leaf)
    (hn : ∀ f, f < fuel → (contract G tcLevel).nodeValid f
      (Generic.nodeCall { g := rowsOf G } (n + 2) tcLevel f))
    {cs bs fs : List Nat} {parents : Parents n}
    (hi : NodeInput G { g := rowsOf G } tcLevel fuel true ⟨level, numcells, cs, st⟩ bs fs parents) :
    let ctx : Ctx n := { g := rowsOf G }
    let out := Engine.node true ctx (n + 2) tcLevel fuel level numcells st
    out.1 = .unwind (level - 1) false ∧
      ∃ targets key, Generation.RefPath ctx tcLevel out.2.allsamelevel level
        (st.refined ctx level numcells) targets key ∧
        Generation.Matches ctx level out.2.view targets key :=
  ⟨firstPath_returns hp hn hi, firstPath_witness hp hn hi⟩

end Hex.GraphIso.Nauty.Engine.Max
