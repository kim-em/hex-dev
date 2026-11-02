/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import all HexGroebner.MatrixState
import all HexGroebner.MatrixStateProof
import all HexGroebner.EliminationOutcome
import all HexGroebner.EliminationScanStep
import all HexGroebner.EliminationKernel
import all HexGroebner.EliminationWorkProof
public import HexGroebner.EliminationScanProof
public import HexGroebner.EliminationScanStep
public import Std.Do
meta import Std.Tactic.Do

public section

/-! Owning scan correspondence proofs inspect private phase bodies. Public
State construction stays behind the executable API. -/

namespace Hex.Groebner

private def returnedScan (initial : Scan) (data : Native.Scan.State) : Scan :=
  { initial with
    dense := data.dense
    last := data.last
    chargedUntil := data.chargedUntil
    leading := if data.leading == 0 then none else some (data.leading-1)
    sugar := data.sugar }

/-- A completed reference scan remembers its final bounded transition, before
normalization. The continuation performs normalization in that same phase. -/
private def scanReturn (base : MatrixState.State) (initial result : Scan) (stats : MatrixStats) : Prop :=
  ∃ (data : Native.Scan.State) (quanta : Nat) (before after : MatrixStats)
      (output : Native.Scan.Result),
    let current := scanState base data (quanta+1) before
    current.geometry ∧ outcome current = outcome base ∧
    Native.Scan.portable current.field.modulus current.slots current.nativePivots current.scan
      4096 (current.limits.work-current.stats.work) 0 false = output ∧
    (Matrix.work base.limits output.work).run before = (.ok (),after) ∧
    output.status = 1 ∧ result = returnedScan initial output.state ∧
    stats = { after with reductions := after.reductions+output.reductions }

private theorem scan_untraced (modulus : UInt64) (slots : ByteArray)
    (pivots : Array Native.Scan.Pivot) (initial : Native.Scan.State) (quantum work traces : Nat) :
    Native.Scan.portable modulus slots pivots initial quantum work traces false =
      Native.Scan.portable modulus slots pivots initial quantum work 0 false := rfl

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 2000000 in
set_option linter.deprecated.syntax false in
open Std.Do in
private theorem nativeScan_spec (base : MatrixState.State) (initial : Scan)
    (hphase : base.phase = .scan) (hgeometry : base.geometry)
    (hstart : base.scan = {
      dense := initial.dense
      column := base.scan.column
      last := initial.last
      chargedUntil := initial.chargedUntil
      sugar := initial.sugar })
    (hquanta : base.quanta = MatrixState.scanFuel base.columns) :
    Triple (m := Matrix.Work) (ps := .except MatrixError (.arg MatrixStats .pure))
      (nativeScan base.field base.limits base.columns base.slots base.pivots base.nativePivots
        base.scan.column initial false)
      (fun stats => ⌜stats = base.stats⌝)
      (fun result stats => ⌜scanReturn base initial result stats⌝,
        fun error stats => ⌜outcome base = (.error error,stats)⌝,PUnit.unit) := by
  have fresh := hstart.symm
  clear hstart
  unfold nativeScan
  simp only [Native.Scan.transition,Native.Scan.untraced_events,scan_untraced]
  mvcgen invariants
  · Invariant.withEarlyReturnNewDo
      (onReturn := fun result _ stats => ⌜scanReturn base initial result stats⌝)
      (onContinue := fun cursor pair stats => ⌜
        (scanState base pair.1 cursor.suffix.length stats).geometry ∧
        outcome (scanState base pair.1 cursor.suffix.length stats) = outcome base ∧
        pair.2.1 = initial.trace ∧ pair.2.2 = initial.node⌝)
      (onExcept := (fun error stats => ⌜outcome base = (.error error,stats)⌝,PUnit.unit))
  all_goals try simp_all [takeDense]
  case vc2.pre =>
    change (scanState base base.scan (MatrixState.scanFuel base.columns) base.stats).geometry ∧
      outcome (scanState base base.scan (MatrixState.scanFuel base.columns) base.stats) = outcome base
    rw [← hquanta,scan_self base hphase]
    exact ⟨hgeometry,rfl⟩
  case vc4.post.success.h_2 =>
    rename_i initialStats hstats result hnone stats hinv
    have last := scan_zero (scanState base result.2.1 0 stats) rfl hinv.1 rfl
    exact hinv.2.1.symm.trans (by simpa only [scanState] using last)
  case vc1.step =>
    rename_i initialStats hstats pref cur suff hlist pair stats hinv
    let current := scanState base pair.2.1 (suff.length+1) stats
    have geometry : current.geometry := hinv.2.1
    have same : outcome current = outcome base := hinv.2.2.1
    generalize houtput : Native.Scan.portable _ _ _ _ _ _ _ _ = output at *
    simp only [Matrix.Work.pre]
    cases hw : (Matrix.work base.limits output.work).run stats with
    | mk result workStats =>
      cases result with
      | error error =>
        have failed := scan_work_error current output error workStats rfl geometry
          (by simp [current,scanState]) houtput hw
        simpa [ExceptT.run,hw] using same.symm.trans failed
      | ok value =>
        cases value
        simp only [ExceptT.run] at hw
        simp only [ExceptT.run,hw]
        by_cases hs1 : output.status = 1
        · simp [hs1,Std.Do.WP.wp,ExceptT.run,ExceptT.mk,ExceptT.pure,
            StateT.pure,StateT.run,Pure.pure,Id.run]
          refine ⟨pair.2.1,suff.length,stats,workStats,output,geometry,same,houtput,?_,hs1,?_,rfl⟩
          · simpa [ExceptT.run] using hw
          · simp [returnedScan]
        · have step := same.symm.trans (scan_pending current rfl geometry
            (by simp [current,scanState]) (by simpa [current,scanState,houtput] using hs1))
          dsimp only [current,scanState] at step
          rw [houtput] at step
          simp only [ExceptT.run,hw] at step
          by_cases hs0 : output.status = 0
          · have bounds := MatrixState.scan_bounds current (base.limits.work-stats.work)
              geometry.1 (by simpa [current,scanState,houtput] using (show output.status ≠ 4 by simp [hs0]))
            dsimp only [current,scanState] at bounds
            rw [houtput] at bounds
            have hdense : output.state.dense.size = current.scan.dense.size :=
              bounds.1.trans geometry.1.symm
            change outcome base = scanPending current output
              { workStats with reductions := workStats.reductions+output.reductions } at step
            rw [scan_continue current output _ rfl geometry hdense hs0] at step
            have nextGeometry := scan_geometry current output.state (current.quanta-1)
              { workStats with reductions := workStats.reductions+output.reductions }
              rfl geometry hdense (Nat.sub_le _ _)
            change (scanState base output.state suff.length _).geometry at nextGeometry
            change outcome base = outcome (scanState base output.state suff.length _) at step
            simp [hs0,Std.Do.WP.wp,ExceptT.run,ExceptT.mk,ExceptT.pure,
              StateT.pure,StateT.run,Pure.pure,Id.run]
            exact ⟨nextGeometry,step.symm⟩
          · by_cases hs2 : output.status = 2
            all_goals by_cases hs3 : output.status = 3
            all_goals simpa [scanPending,hs1,hs0,hs2,hs3,Std.Do.WP.wp,
              ExceptT.run,ExceptT.mk,ExceptT.pure,StateT.pure,StateT.run,Pure.pure,Id.run,
              MonadExcept.throw,MonadExceptOf.throw,throwThe] using step

#print axioms nativeScan_spec

end Hex.Groebner
