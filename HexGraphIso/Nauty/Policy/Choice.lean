/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Tracking
import all HexGraphIso.Nauty.Policy.Tracking
import all HexGraphIso.Nauty.Policy.RouteState
import all HexGraphIso.Nauty.Policy.Route
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- A live target is canonical or is the target saved by the first descent. -/
def Choice (ctx : Ctx n) (tcLevel level tc : Nat) (st : Search n) : Prop :=
  st.eqlevFirst = level → specTargetcell ctx st.lab st.ptn level tcLevel = tc ∨
    st.firsttc[level]! = Int.ofNat tc

/-- The cheap guard leaves the chosen target and its live comparison unchanged. -/
theorem Choice.cheap {ctx : Ctx n} {tcLevel level tc : Nat} {st : Search n}
    (h : Choice ctx tcLevel level tc st) (first : Bool) :
    Choice ctx tcLevel level tc (cheapCheck first level st) := by
  unfold cheapCheck
  split <;> exact h

/-- An equitable guided endpoint makes the engine's retained target
canonical or equal to the saved first target. -/
theorem GuidedState.choice {ctx : Ctx n} {tcLevel base level numcells : Nat}
    {root : RefineSt n} {st : Search n}
    (h : GuidedState ctx tcLevel base root level level numcells st)
    (hok : IterOk ctx base root) (heq : Equitable ctx base root.lab root.ptn)
    (hacc : bcount root.ptn base n = root.numcells)
    (hnc : numcells < n) (hlevel : 0 < level)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u) :
    let r := chooseTarget false ctx tcLevel level numcells st
    Choice ctx tcLevel level r.1.toNat r.2.2.2 := by
  intro r hkeep
  have hold : st.eqlevFirst = level := by
    have hle := chooseTarget_le ctx tcLevel level numcells st
    have hb := h.bound
    change r.2.2.2.eqlevFirst ≤ st.eqlevFirst at hle
    omega
  have hequitable := (h.descent hold).equitable hok heq hacc hsymm
  obtain ⟨current, hh, hl, hp, _⟩ := h.descent hold
  have hit := hh.iter hok
  have hls : st.lab.size = n := by rw [← hl]; exact hit.ok.labSize
  have hps : st.ptn.size = n := by rw [← hp]; exact hit.ok.ptnSize
  have hLab : LabOk st.lab n := by rw [← hl]; exact hit.ok.labOk
  have hend : st.ptn[st.ptn.size - 1]! ≤ level := by rw [← hp]; exact hit.ok.ptnEnd
  have hfields := chooseTarget_fields ctx tcLevel level numcells st
  change r.2.2.2 = { st with eqlevFirst := r.2.2.2.eqlevFirst, tctotal := r.2.2.2.tctotal } at hfields
  by_cases hcomp : st.compCanon < 0
  · right
    have ht := chooseTarget_hinted hnc hlevel hold hcomp hkeep
    have hc := chooseTarget_cast (ctx := ctx) (tcLevel := tcLevel) hnc hold
    change Int.ofNat r.1.toNat = r.1 at hc
    rw [hfields, hc]
    exact ht.symm
  · left
    have ht := chooseTarget_unhinted (tcLevel := tcLevel) hnc (by omega) hequitable hLab hls hps hend
    change r.1 = Int.ofNat (specTargetcell ctx st.lab st.ptn level tcLevel) at ht
    rw [hfields, ht]
    rfl

/-- A recovered parent retains its canonical-or-saved target even when
its labels were reordered by the child. -/
theorem Choice.recover {G : Colored n k} {ctx : Ctx n} {tcLevel level numcells tc : Nat}
    {st out : Search n} (h : Choice ctx tcLevel level tc st)
    (hb : st.eqlevFirst ≤ level) (hlevel : 1 ≤ level) (hn0 : 0 < n)
    (hok : SearchOk G level numcells st) (hout : SearchOut G level level st out)
    (ht : out.firsttc = st.firsttc) (hd : st.eqlevFirst < level → out.eqlevFirst < level) :
    Choice ctx tcLevel level tc (recoverLevels level (recoverPtn (n + 2) level out)) := by
  intro hkeep
  have hold : st.eqlevFirst = level := by
    by_cases he : st.eqlevFirst = level
    · exact he
    · have hdiv := hd (by omega)
      rw [recover_eqlev] at hkeep
      omega
  have hr := (referencePolicy ctx (n + 2) tcLevel).recover level out
  have htc : (recoverLevels level (recoverPtn (n + 2) level out)).firsttc = st.firsttc :=
    (congrArg (fun r : Array Nat × Array Int × Array Nat => r.2.1) hr).trans ht
  rcases h hold with hcanonical | hsaved
  · left
    have hl : (recoverLevels level (recoverPtn (n + 2) level out)).lab = out.lab := by
      have he := congrArg Search.lab (recover_eq (n + 2) level out)
      change (recoverLevels level (recoverPtn (n + 2) level out)).lab = _ at he
      rw [Nauty.recover_lab] at he
      exact he
    rw [hl, recover_ptn_eq hok hout]
    have hperm : cellsPerm st.ptn level st.lab out.lab := hout.perm
    exact (specTargetcell_perm hperm (by change n ≤ st.ptn.size; rw [hok.ptnSize]; omega)
      (searchOk_end hn0 hok hlevel)).symm.trans hcanonical
  · right
    rw [htc]
    exact hsaved

/-- The actual child call supplies the frame and divergence properties
needed to retain its parent's choice after recovery. -/
theorem Choice.child_return {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells tc tv : Nat} {st : Search n} {cell : VSet n}
    (h : Choice ctx tcLevel level tc st) (hb : st.eqlevFirst ≤ level) (first : Bool)
    (hlevel : 1 ≤ level) (hok : SearchOk G level numcells st)
    (htarget : Generic.Target (fun st => st) level tc cell st) (htv : cell.mem tv = true) :
    let out := (node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (Nauty.child first level tc tv st)).2
    Choice ctx tcLevel level tc (recoverLevels level (recoverPtn (n + 2) level
      { out with fixedpts := out.fixedpts.erase tv })) := by
  let ch := Nauty.child first level tc tv st
  let out := (node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1) ch).2
  have hn0 : 0 < n := by have := VSet.mem_lt htv; omega
  have hch := (reachPolicy G ctx tcLevel hn0).child first level numcells tc tv cell st
    hlevel hok htarget htv
  have ho := node_out false hn0 (by omega) hch.1 (ctx := ctx) (tcLevel := tcLevel) (fuel := fuel)
  have hout : SearchOut G level level st out := hch.2 _
    (by simpa only [Nat.add_sub_cancel, policy, Generic.Policy.child] using ho)
  have ht : out.firsttc = st.firsttc := by
    have hr := node_reference ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1) ch
    have hc := congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1) hr
    change out.firsttc = ch.firsttc at hc
    cases first <;> exact hc
  have hd : st.eqlevFirst < level → out.eqlevFirst < level := by
    intro hlow
    apply node_diverged (by omega)
    cases first <;> exact hlow
  exact h.recover hb hlevel hn0 hok (hout.congr rfl rfl rfl rfl) ht hd

end Hex.GraphIso.Nauty
