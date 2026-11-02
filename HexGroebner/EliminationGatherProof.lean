/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import all HexGroebner.MatrixState
import all HexGroebner.MatrixStateProof
import all HexGroebner.EliminationOutcome
import all HexGroebner.EliminationPhaseProof
import all HexGroebner.EliminationGatherStep
import all HexGroebner.Elimination
import all HexGroebner.EliminationWorkProof
public import HexGroebner.EliminationGatherStep
public import Std.Do
meta import Std.Tactic.Do

public section

/-! Owning gather correspondence proofs may inspect private phase bodies.
Do not expose public unchecked State builders from this module. -/

namespace Hex.Groebner

private theorem gather_geometry (base : MatrixState.State) (data : Native.Gather.State)
    (quanta : Nat) (stats : MatrixStats) (hphase : base.phase = .gather)
    (hgeometry : base.geometry) (hdense : data.dense.size = base.gather.dense.size)
    (hquanta : quanta ≤ base.quanta) : (gatherState base data quanta stats).geometry := by
  simp only [MatrixState.State.geometry,hphase] at hgeometry
  simp only [gatherState,MatrixState.State.geometry]
  exact ⟨hdense.trans hgeometry.1,hgeometry.2.1,hgeometry.2.2.1,
    Nat.le_trans hquanta hgeometry.2.2.2⟩

private theorem gather_continue (state : MatrixState.State) (output : Native.Gather.Result)
    (stats : MatrixStats) (hphase : state.phase = .gather) (hgeometry : state.geometry)
    (hdense : output.state.dense.size = state.gather.dense.size) (hstatus : output.status = 0) :
    gatherTail state output stats = outcome (gatherState state output.state (state.quanta-1) stats) := by
  have geometry := gather_geometry state output.state (state.quanta-1) stats hphase hgeometry
    hdense (Nat.sub_le _ _)
  by_cases hlast : state.quanta = 1
  · have last := gather_zero (gatherState state output.state (state.quanta-1) stats) rfl geometry
      (by simp [gatherState,hlast])
    simpa [gatherTail,hstatus,hlast,gatherState] using last.symm
  · simp [gatherTail,hstatus,hlast]

private theorem gather_complete (state : MatrixState.State) (output : Native.Gather.Result)
    (stats : MatrixStats) (hstatus : output.status = 1) :
    gatherTail state output stats = outcome (gatheredState state
      ⟨output.state.columns,output.state.coefficients⟩ output.state.dense (state.quanta-1) stats) := by
  simp [gatherTail,hstatus]

private theorem gather_self (base : MatrixState.State) (hphase : base.phase = .gather) :
    gatherState base base.gather base.quanta base.stats = base := by
  unfold gatherState
  rw [← hphase]

private theorem gathered_update (base : MatrixState.State) (data : Native.Gather.State)
    (oldQuanta : Nat) (oldStats : MatrixStats) (row : SparseRow) (dense : ByteArray)
    (quanta : Nat) (stats : MatrixStats) (hphase : base.phase = .gather) :
    gatheredState (gatherState base data oldQuanta oldStats) row dense quanta stats =
      gatheredState base row dense quanta stats := by
  unfold gatheredState gatherState
  simp only [hphase]

-- Each charge case uses the same transformer normalization rules.
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 2000000 in
set_option linter.deprecated.syntax false in
open Std.Do in
private theorem nativeGather_spec (base : MatrixState.State) (hphase : base.phase = .gather)
    (hgeometry : base.geometry)
    (hstart : base.gather = ⟨base.gather.dense,{},{},base.leading⟩)
    (hquanta : base.quanta = (base.scan.last+1-base.leading+4095)/4096+1) :
    Triple (m := Matrix.Work) (ps := .except MatrixError (.arg MatrixStats .pure))
      (nativeGather base.field base.limits base.gather.dense base.leading base.scan.last base.inverse)
      (fun stats => ⌜stats = base.stats⌝)
      (fun result stats => ⌜∃ quanta,
          (gatheredState base result.1 result.2 quanta stats).geometry ∧ outcome
          (gatheredState base result.1 result.2 quanta stats) = outcome base⌝,
        fun error stats => ⌜outcome base = (.error error,stats)⌝,PUnit.unit) := by
  have fresh := hstart.symm
  clear hstart
  unfold nativeGather
  simp only [Native.Gather.gather]
  mvcgen invariants
  · Invariant.withEarlyReturnNewDo
      (onReturn := fun result _ stats => ⌜∃ quanta,
        (gatheredState base result.1 result.2 quanta stats).geometry ∧ outcome
        (gatheredState base result.1 result.2 quanta stats) = outcome base⌝)
      (onContinue := fun cursor data stats => ⌜
        (gatherState base data cursor.suffix.length stats).geometry ∧
        outcome (gatherState base data cursor.suffix.length stats) = outcome base⌝)
      (onExcept := (fun error stats => ⌜outcome base = (.error error,stats)⌝,PUnit.unit))
  all_goals try simp_all
  case vc2.pre =>
    rw [← hquanta,gather_self base hphase]
    exact ⟨hgeometry,rfl⟩
  case vc4.post.success.h_2 =>
    rename_i initialStats result stats hstats hnone hinv
    have last := gather_zero (gatherState base result.2 0 stats) rfl hinv.1 rfl
    exact hinv.2.symm.trans (by simpa only [gatherState] using last)
  case vc1.step =>
    rename_i initialStats pref cur suff pair stats hstats hlist hinv
    let current := gatherState base pair.2 (suff.length+1) stats
    have currentGeometry : current.geometry := hinv.2.1
    have step := hinv.2.2.symm.trans (gather_outcome current rfl currentGeometry (by simp [current,gatherState]))
    dsimp only [current,gatherState] at step
    generalize houtput : Native.Gather.portable _ _ _ _ _ _ _ _ = output at *
    have hdense := Native.Gather.dense_size base.field.modulus pair.2 (base.scan.last+1) 4096
      (base.limits.outputEntries-stats.outputEntries)
      (base.limits.packedBytes-stats.packedBytes) (base.limits.work-stats.work) base.inverse
    rw [houtput] at hdense
    simp only [Matrix.Work.pre]
    simp only [gatherCharges,ExceptT.run,ExceptT.mk,ExceptT.bind,ExceptT.bindCont,StateT.bind,StateT.pure,Bind.bind,Pure.pure] at step
    cases he : (Matrix.charge .outputEntries output.entries base.limits.outputEntries
        (·.outputEntries) fun stats n => { stats with outputEntries := n }).run stats with
    | mk entries entriesStats =>
      simp only [ExceptT.run] at he
      cases entries
      all_goals try simp [ExceptT.run,he,Std.Do.WP.wp,Pure.pure,StateT.run,Id.run,StateT.bind,StateT.pure,ExceptT.bindCont,ExceptT.mk,ExceptT.pure,Bind.bind] at step ⊢
      all_goals try exact step
      all_goals
        cases hb : (Matrix.packedBytes base.limits output.bytes).run entriesStats with
        | mk bytes bytesStats =>
          simp only [ExceptT.run] at hb
          cases bytes
          all_goals try simp [ExceptT.run,hb,Std.Do.WP.wp,Pure.pure,StateT.run,Id.run,StateT.bind,StateT.pure,ExceptT.bindCont,ExceptT.mk,ExceptT.pure,Bind.bind] at step ⊢
          all_goals try exact step
          all_goals
            cases hw : (Matrix.work base.limits output.work).run bytesStats with
            | mk work finalStats =>
              simp only [ExceptT.run] at hw
              cases work
              all_goals try simp [ExceptT.run,hw,Std.Do.WP.wp,Pure.pure,StateT.run,Id.run,StateT.bind,StateT.pure,ExceptT.bindCont,ExceptT.mk,ExceptT.pure,Bind.bind] at step ⊢
              all_goals try exact step
              all_goals
                change outcome base = gatherTail current output finalStats at step
                by_cases hs1 : output.status = 1
                · rw [gather_complete current output finalStats hs1] at step
                  have hcount : current.quanta-1 = suff.length := by simp [current,gatherState]
                  rw [hcount] at step
                  have finish : outcome (gatheredState base
                      ⟨output.state.columns,output.state.coefficients⟩ output.state.dense
                      suff.length finalStats) = outcome base := by
                    simpa [current,gathered_update,hphase] using step.symm
                  simp [hs1,Std.Do.WP.wp,ExceptT.run,ExceptT.mk,ExceptT.pure,
                    StateT.pure,StateT.run,Pure.pure,Id.run]
                  have completeGeometry := gathered_geometry base
                    ⟨output.state.columns,output.state.coefficients⟩ output.state.dense
                    suff.length finalStats (hdense.trans currentGeometry.1)
                  exact ⟨suff.length,completeGeometry,finish⟩
                · by_cases hs0 : output.status = 0
                  · rw [gather_continue current output finalStats rfl currentGeometry hdense hs0] at step
                    have nextGeometry := gather_geometry current output.state (current.quanta-1)
                      finalStats rfl currentGeometry hdense (Nat.sub_le _ _)
                    change (gatherState base output.state suff.length finalStats).geometry at nextGeometry
                    change outcome base = outcome (gatherState base output.state suff.length finalStats) at step
                    simp [hs0,Std.Do.WP.wp,ExceptT.run,ExceptT.mk,ExceptT.pure,
                      StateT.pure,StateT.run,Pure.pure,Id.run]
                    exact ⟨nextGeometry,step.symm⟩
                  · by_cases hs2 : output.status = 2
                    all_goals by_cases hs3 : output.status = 3
                    all_goals by_cases hs4 : output.status = 4
                    all_goals by_cases hs5 : output.status = 5
                    all_goals simpa [gatherTail,hs1,hs0,hs2,hs3,hs4,hs5,Std.Do.WP.wp,
                      ExceptT.run,ExceptT.mk,ExceptT.pure,StateT.pure,StateT.run,Pure.pure,Id.run,
                      MonadExcept.throw,MonadExceptOf.throw,throwThe] using step




#print axioms nativeGather_spec
#print axioms gather_continue

end Hex.Groebner
