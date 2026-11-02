/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import all HexGroebner.MatrixState
import all HexGroebner.Matrix
import all HexGroebner.MatrixValidation
import all HexGroebner.MatrixStateProof
import all HexGroebner.EliminationInvariant
import all HexGroebner.EliminationOutcome
import all HexGroebner.EliminationWorkProof
import all HexGroebner.EliminationPhaseProof
import all HexGroebner.EliminationValidationProof
import all HexGroebner.EliminationInputProof
import all HexGroebner.EliminationScanProof
import all HexGroebner.EliminationScanStep
import all HexGroebner.EliminationScanLoop
import all HexGroebner.EliminationGatherStep
import all HexGroebner.EliminationGatherProof
import all HexGroebner.EliminationOrderProof
import all HexGroebner.EliminationKernel
public import HexGroebner.EliminationKernel
public import HexGroebner.EliminationInvariant
public import HexGroebner.EliminationInputProof
public import HexGroebner.EliminationScanLoop
public import HexGroebner.EliminationGatherProof
public import HexGroebner.EliminationOrderProof
public import Std.Do
meta import Std.Tactic.Do

public section

/-! Owning whole-eliminator correspondence proofs inspect private phase bodies.
State construction stays behind the executable API. -/

namespace Hex.Groebner

open Std.Do

@[spec] private theorem nativeScan_run (field : PrimeField) (limits : MatrixLimits)
    (columns : Nat) (slots : ByteArray) (pivots : Array Pivot) (nativePivots : Array Native.Scan.Pivot)
    (first : Nat) (scan : Scan) (post : Matrix.Work.Post Scan) :
    Triple (nativeScan field limits columns slots pivots nativePivots first scan false)
      (Matrix.Work.pre (nativeScan field limits columns slots pivots nativePivots first scan false) post)
      post := Matrix.Work.triple_run _ post

@[spec] private theorem nativeGather_run (field : PrimeField) (limits : MatrixLimits)
    (dense : ByteArray) (first last : Nat) (inverse : UInt64)
    (post : Matrix.Work.Post (SparseRow × ByteArray)) :
    Triple (nativeGather field limits dense first last inverse)
      (Matrix.Work.pre (nativeGather field limits dense first last inverse) post) post :=
  Matrix.Work.triple_run _ post

-- Shared transformer rules cover distinct successful and failed charge branches.
set_option linter.unusedSimpArgs false in
set_option linter.deprecated.syntax false in
set_option maxHeartbeats 2000000 in
private theorem eliminate_spec (field : PrimeField) (limits : MatrixLimits) (columns : Nat)
    (reducers targets : Array SparseRow) (sugars : Array Nat) (independent : Bool) :
    let base := MatrixState.start field limits columns reducers targets sugars independent
    Triple (m := Matrix.Work) (ps := .except MatrixError (.arg MatrixStats .pure))
      (eliminate field limits columns reducers targets false sugars true independent)
      (fun stats => ⌜stats = {}⌝)
      (fun result stats => ⌜outcome base = (.ok result,stats)⌝,
        fun error stats => ⌜outcome base = (.error error,stats)⌝,PUnit.unit) := by
  dsimp only
  unfold eliminate
  simp only [record_untraced,Matrix.zerosWith_spec,scatter_loop,order_loop,
    Bool.false_eq_true,ite_false,ite_true]
  mvcgen
  all_goals
    have checked := check_outcome
      (MatrixState.start field limits columns reducers targets sugars independent) rfl
  all_goals try solve | simpa [MatrixState.start, *] using checked
  case vc5.isFalse.isFalse.isFalse.isFalse =>
    rename_i hdims hcolumns hrows hsugars stats hstats
    subst stats
    simp only [Matrix.Work.pre]
    have validated := validation_outcome
      { (MatrixState.start field limits columns reducers targets sugars independent) with phase := .validate } rfl
    simp only [MatrixState.start] at validated checked
    have dimensions : ¬(columns > 4294967295 ∨ reducers.size+targets.size > 4294967295) := by
      simpa only [Bool.or_eq_true,decide_eq_true_eq] using hdims
    simp [Bool.or_eq_true,dimensions,hcolumns,hrows,hsugars] at checked
    rw [Matrix.validateFrom_zero field limits columns reducers targets true] at validated
    have frontend := checked.trans validated
    cases hv : (Matrix.validateRows field limits columns reducers targets true).run {} with
    | mk result stats =>
      simp only [ExceptT.run] at hv
      cases result with
      | error error =>
        simpa [MatrixState.start,ExceptT.run,hv,validationTail,Std.Do.WP.wp,StateT.run,Pure.pure,Id.run] using frontend
      | ok value =>
        cases value
        simp only [ExceptT.run,hv,validationTail] at frontend ⊢
        let workspace : MatrixState.State :=
          { (MatrixState.start field limits columns reducers targets sugars independent) with
            phase := .workspace
            validation := max 0 (reducers.size+targets.size)
            stats := stats }
        have setup := frontend.trans (workspace_outcome workspace rfl)
        mvcgen
        case vc1.mk.ok.unit.isTrue =>
          rename_i hsize
          simpa [workspace,MatrixState.start,hsize] using setup
        case vc2.mk.ok.unit.isFalse =>
          rename_i hsize
          simp only [workspace,MatrixState.start] at setup
          simp only [hsize,ite_false] at setup
          simp only [Matrix.Work.pre]
          cases hb : (Matrix.packedBytes limits (columns*(field.width.bytes+4))).run stats with
          | mk bytes bytesStats =>
            simp only [ExceptT.run] at hb
            cases bytes with
            | error error =>
              simpa [MatrixState.start,workspaceTail,ExceptT.run,ExceptT.mk,ExceptT.bind,
                ExceptT.bindCont,StateT.bind,StateT.pure,Bind.bind,Pure.pure,hb,
                Std.Do.WP.wp,StateT.run,Id.run] using setup
            | ok value =>
              cases value
              simp only [ExceptT.run,hb]
              mvcgen
              simp only [Matrix.Work.pre]
              cases hw : (Matrix.work limits (columns*(field.width.bytes+4))).run bytesStats with
              | mk work workStats =>
                simp only [ExceptT.run] at hw
                cases work with
                | error error =>
                  simpa [MatrixState.start,workspaceTail,ExceptT.run,ExceptT.mk,ExceptT.bind,
                    ExceptT.bindCont,StateT.bind,StateT.pure,Bind.bind,Pure.pure,hb,hw,
                    Std.Do.WP.wp,StateT.run,Id.run] using setup
                | ok value =>
                  cases value
                  simp only [ExceptT.run,hw]
                  mvcgen invariants
                  · (fun ⟨cursor,pair⟩ stats => ⌜atInput
                        (MatrixState.start field limits columns reducers targets sugars independent)
                        cursor.prefix.length pair.1 pair.2.1 pair.2.2.1 pair.2.2.2.1
                        pair.2.2.2.2.1 pair.2.2.2.2.2.1 pair.2.2.2.2.2.2 stats⌝,
                      fun error stats => ⌜outcome
                        (MatrixState.start field limits columns reducers targets sugars independent) =
                          (.error error,stats)⌝,PUnit.unit)
                  case vc2.vc1.mk.ok.unit.mk.ok.unit.pre =>
                    let ready : MatrixState.State :=
                      { (MatrixState.start field limits columns reducers targets sugars independent) with
                        phase := .input
                        validation := max 0 (reducers.size+targets.size)
                        dense := Matrix.zeros (columns*field.width.bytes)
                        slots := Matrix.zeros (columns*4)
                        stats := workStats }
                    have same : outcome ready = outcome
                        (MatrixState.start field limits columns reducers targets sugars independent) := by
                      simpa [ready,MatrixState.start,workspaceTail,ExceptT.run,ExceptT.mk,
                        ExceptT.bind,ExceptT.bindCont,StateT.bind,StateT.pure,Bind.bind,Pure.pure,hb,hw]
                        using setup.symm
                    refine ⟨rfl,ready,?_,rfl,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,same⟩
                    · rfl
                    · simp [ready,MatrixState.start,MatrixState.State.geometry,Matrix.zeros_size]
                  case vc3.vc1.mk.ok.unit.mk.ok.unit.post.success.isTrue =>
                    rename_i pair hindependent finalStats hinv
                    have invariant : atInput
                        (MatrixState.start field limits columns reducers targets sugars independent)
                        (reducers.size+targets.size) pair.1 pair.2.1 pair.2.2.1 pair.2.2.2.1
                        pair.2.2.2.2.1 pair.2.2.2.2.2.1 pair.2.2.2.2.2.2 finalStats := by
                      simpa [Std.Legacy.Range.toList] using hinv
                    have finish := input_finish _ _ _ _ _ _ _ _ _ invariant
                    simpa only [MatrixState.start,hindependent,ite_true] using finish
                  case vc4.vc1.mk.ok.unit.mk.ok.unit.post.success.isFalse =>
                    rename_i pair hindependent finalStats hinv
                    have invariant : atInput
                        (MatrixState.start field limits columns reducers targets sugars independent)
                        (reducers.size+targets.size) pair.1 pair.2.1 pair.2.2.1 pair.2.2.2.1
                        pair.2.2.2.2.1 pair.2.2.2.2.2.1 pair.2.2.2.2.2.2 finalStats := by
                      simpa [Std.Legacy.Range.toList] using hinv
                    have finish := input_finish _ _ _ _ _ _ _ _ _ invariant
                    simp only [MatrixState.start,hindependent,ite_false] at finish
                    simp only [Matrix.Work.pre]
                    cases hf : (Matrix.work limits columns).run finalStats with
                    | mk result stats =>
                      simp only [ExceptT.run] at hf
                      cases result
                      all_goals simpa [MatrixState.start,hindependent,ExceptT.run,hf,Std.Do.WP.wp,
                        ExceptT.pure,ExceptT.mk,StateT.pure,Pure.pure,StateT.run,Id.run,ExceptT.bind,
                        ExceptT.bindCont,StateT.bind,Bind.bind] using finish
                  case vc1.step =>
                    rename_i pref cur suff hlist pair rowStats hinv
                    have cursor := range_cursor (reducers.size+targets.size) pref suff cur hlist
                    rcases hinv with ⟨htrace,state,hframe,hphase,hgeometry,hinput,hdense,hslots,
                      hpivots,hnative,hremainders,hrank,hstats,hsame⟩
                    simp only [MatrixState.State.identity,MatrixState.start,Prod.mk.injEq] at hframe
                    rcases hframe with ⟨hfield,hlimits,hcols,hreducers,htargets,hsugars',hindependent⟩
                    have currentInput : state.input = cur := hinput.trans cursor.1.symm
                    have bound : state.input < state.reducers.size+state.targets.size := by
                      rw [hinput,hreducers,htargets]
                      exact cursor.2
                    have charged := hsame.symm.trans (input_outcome state hphase hgeometry bound)
                    simp only [MatrixState.isTarget,currentInput,hfield,hlimits,hcols,hreducers,htargets,
                      hsugars',hstats] at charged
                    simp only [Matrix.Work.pre]
                    cases rowWork : (Matrix.work limits 1).run rowStats with
                    | mk result nextStats =>
                      simp only [ExceptT.run] at rowWork
                      cases result with
                      | error error =>
                        simpa [ExceptT.run,rowWork] using charged
                      | ok value =>
                        cases value
                        simp only [ExceptT.run,rowWork] at charged ⊢
                        mvcgen
                        case vc1.mk.ok.unit.isTrue.isTrue | vc2.mk.ok.unit.isTrue.isFalse =>
                          refine ⟨htrace,zeroInput state (sugars[cur]?.getD 0) nextStats,?_⟩
                          have denseSize : state.dense.size = state.columns*state.field.width.bytes := by
                            simpa only [MatrixState.State.geometry,hphase] using hgeometry
                          simp_all [inputTail,zeroInput,zero_run,MatrixState.State.identity,
                            MatrixState.State.geometry,MatrixState.isTarget,MatrixState.start]
                          all_goals rfl
                        case vc3.mk.ok.unit.isFalse.isTrue =>
                          rename_i hnonzero hquick
                          subst field
                          simp [inputTail,MatrixState.isTarget,currentInput,hreducers,hslots,hquick,
                            hnonzero,hlimits] at charged
                          simp only [Matrix.Work.pre]
                          cases hi : (Matrix.inverse state.field state.field.barrett limits
                              (Packed.read state.field.width
                                (if cur ≥ reducers.size then targets[cur-reducers.size]!
                                  else reducers[cur]!).coefficients 0)).run nextStats with
                          | mk result inverseStats =>
                            simp only [ExceptT.run] at hi
                            cases result with
                            | error error =>
                              simpa [ExceptT.run,hi] using charged
                            | ok inverse =>
                              simp only [ExceptT.run,hi] at charged ⊢
                              mvcgen
                              simp only [Matrix.Work.pre]
                              cases hs : (Matrix.scaleSparse state.field state.field.barrett limits
                                  (if cur ≥ reducers.size then targets[cur-reducers.size]!
                                    else reducers[cur]!) inverse).run inverseStats with
                              | mk result scaleStats =>
                                simp only [ExceptT.run] at hs
                                cases result with
                                | error error =>
                                  simpa [ExceptT.run,hs] using charged
                                | ok output =>
                                  simp only [ExceptT.run,hs] at charged ⊢
                                  mvcgen
                                  all_goals
                                    refine ⟨htrace,installedInput state output
                                      (Packed.read .u32
                                        (if cur ≥ reducers.size then targets[cur-reducers.size]!
                                          else reducers[cur]!).columns 0).toNat
                                      inverse (sugars[cur]?.getD 0) scaleStats,?_⟩
                                    have denseSize : state.dense.size = state.columns*state.field.width.bytes := by
                                      simpa only [MatrixState.State.geometry,hphase] using hgeometry
                                    simp_all [installedInput,install_run,MatrixState.State.identity,
                                      MatrixState.State.geometry,MatrixState.isTarget,MatrixState.start]
                                  all_goals simp_all [Nat.not_le.mpr hquick.1]
                                  all_goals rfl
                        case vc4.mk.ok.unit.isFalse.isFalse =>
                          rename_i hnonzero hscan
                          subst field
                          simp [inputTail,MatrixState.isTarget,currentInput,hreducers,hslots,hscan,
                            hnonzero,hlimits] at charged
                          simp only [Matrix.Work.pre]
                          cases scatterWork : (Matrix.work limits
                              (if cur ≥ reducers.size then targets[cur-reducers.size]!
                                else reducers[cur]!).size).run nextStats with
                          | mk result scatterStats =>
                            simp only [ExceptT.run] at scatterWork
                            cases result with
                            | error error =>
                              simpa [ExceptT.run,scatterWork] using charged
                            | ok value =>
                              cases value
                              simp only [ExceptT.run,scatterWork] at charged ⊢
                              mvcgen
                              let row := if cur ≥ reducers.size then targets[cur-reducers.size]! else reducers[cur]!
                              let scanning := preparedScan state row (sugars[cur]?.getD 0) scatterStats
                              let initial : Scan := {
                                dense := scatterRow state.field.width row pair.1
                                last := (Packed.read .u32 row.columns (row.size-1)).toNat
                                chargedUntil := (Packed.read .u32 row.columns 0).toNat
                                leading := none
                                trace := pair.2.2.2.2.1
                                node := none
                                sugar := sugars[cur]?.getD 0 }
                              have scanGeometry := prepared_geometry state row (sugars[cur]?.getD 0)
                                scatterStats hphase hgeometry bound
                              have contract := nativeScan_spec scanning initial
                                (by simp [scanning,preparedScan]) scanGeometry
                                (by simp [scanning,preparedScan,initial,hdense])
                                (by simp [scanning,preparedScan])
                              have post := triple_post _ scanning.stats _ contract
                              change outcome (MatrixState.start state.field limits columns reducers targets sugars independent) =
                                outcome scanning at charged
                              simp only [Matrix.Work.pre]
                              cases hn : (nativeScan state.field limits columns pair.2.1 pair.2.2.1 pair.2.2.2.1
                                  (Packed.read .u32 row.columns 0).toNat initial false).run scatterStats with
                              | mk result scanStats =>
                                simp only [ExceptT.run] at hn
                                cases result with
                                | error error =>
                                  have failed : outcome scanning = (.error error,scanStats) := by
                                    simpa [scanning,preparedScan,hlimits,hcols,hslots,hpivots,hnative,
                                      ExceptT.run,hn] using post
                                  simpa [ExceptT.run,hn] using charged.trans failed
                                | ok result =>
                                  have returned : scanReturn scanning initial result scanStats := by
                                    simpa [scanning,preparedScan,hlimits,hcols,hslots,hpivots,hnative,
                                      ExceptT.run,hn] using post
                                  simp only [ExceptT.run,hn]
                                  rcases returned with ⟨data,quanta,before,after,output,geometry,same,
                                    transition,workCharge,status,returned,statistics⟩
                                  let current := scanState scanning data (quanta+1) before
                                  have joined : outcome (MatrixState.start state.field limits columns
                                      reducers targets sugars independent) = outcome current := charged.trans same.symm
                                  have fuel : current.quanta ≠ 0 := by simp [current,scanState]
                                  have bounds := MatrixState.scan_bounds current
                                    (current.limits.work-current.stats.work) geometry.1
                                    (by rw [transition]; simp [status])
                                  rw [transition] at bounds
                                  subst result
                                  subst scanStats
                                  by_cases leading : output.state.leading = 0
                                  · have finish := scan_complete_zero current output after rfl geometry fuel
                                      transition workCharge status leading
                                    have complete := joined.trans finish
                                    simp [returnedScan,initial,leading]
                                    all_goals try mvcgen
                                    all_goals
                                      refine ⟨htrace,zeroScanned current output.state (current.quanta-1)
                                        { after with reductions := after.reductions+output.reductions },?_⟩
                                      simp_all [zeroScanned,zero_run,current,scanState,scanning,preparedScan,
                                        MatrixState.State.identity,MatrixState.State.geometry,
                                        MatrixState.isTarget,MatrixState.start]
                                    all_goals rfl
                                  · have normalization := joined.trans (scan_normalize current output after
                                      rfl geometry fuel transition workCharge status leading)
                                    cases hi : (scanInverse current output.state).run
                                        { after with reductions := after.reductions+output.reductions } with
                                    | mk result inverseStats =>
                                      simp only [ExceptT.run] at hi
                                      cases result with
                                      | error error =>
                                        simp only [ExceptT.run,hi] at normalization
                                        by_cases independentRow :
                                            independent = true ∧ cur ≥ reducers.size
                                        all_goals
                                          have inverseRun := hi
                                          simp [scanInverse,current,scanState,scanning,preparedScan,
                                            MatrixState.isTarget,currentInput,hreducers,hindependent,hlimits,
                                            Bool.and_eq_true,decide_eq_true_eq,independentRow,ite_true,ite_false]
                                            at inverseRun
                                        all_goals try
                                          change (Except.ok (1 : UInt64),
                                            { after with reductions := after.reductions+output.reductions }) =
                                            (.error error,inverseStats) at inverseRun
                                          cases (Prod.mk.inj inverseRun).1
                                        all_goals simp [returnedScan,initial,leading,Bool.and_eq_true,independentRow]
                                        all_goals mvcgen
                                        all_goals simpa [Matrix.Work.pre,ExceptT.run,inverseRun] using normalization
                                      | ok inverse =>
                                        simp only [ExceptT.run,hi] at normalization
                                        by_cases independentRow :
                                            independent = true ∧ cur ≥ reducers.size
                                        all_goals simp [returnedScan,initial,leading,Bool.and_eq_true,independentRow]
                                        all_goals first
                                          | (have direct : (1 : UInt64) = inverse ∧
                                                { after with reductions := after.reductions+output.reductions } =
                                                  inverseStats := by
                                                have equation := hi
                                                simp only [scanInverse,current,scanState,scanning,preparedScan,
                                                  MatrixState.isTarget,currentInput,hreducers,hindependent,
                                                  Bool.and_eq_true,decide_eq_true_eq,independentRow,ite_true]
                                                  at equation
                                                change (Except.ok (1 : UInt64),
                                                  { after with reductions := after.reductions+output.reductions }) =
                                                  (.ok inverse,inverseStats) at equation
                                                exact ⟨Except.ok.inj (Prod.mk.inj equation).1,
                                                  (Prod.mk.inj equation).2⟩
                                             rw [direct.1,direct.2])
                                          | (have inverseRun := hi
                                             simp only [scanInverse,current,scanState,scanning,preparedScan,
                                               MatrixState.isTarget,currentInput,hreducers,hindependent,hlimits,
                                               Bool.and_eq_true,decide_eq_true_eq,independentRow,ite_false]
                                               at inverseRun
                                             mvcgen
                                             simp only [Matrix.Work.pre,ExceptT.run,inverseRun])
                                        all_goals mvcgen
                                        all_goals simp only [Matrix.Work.pre]
                                        all_goals
                                          cases gatherWork : (Matrix.work limits
                                              (output.state.last+1-(output.state.leading-1))).run inverseStats with
                                          | mk result gatherStats =>
                                            simp only [ExceptT.run] at gatherWork
                                            cases result with
                                            | error error =>
                                              simpa [current,scanState,scanning,preparedScan,hlimits,
                                                ExceptT.run,gatherWork,independentRow,MatrixState.start]
                                                using normalization
                                            | ok value =>
                                              cases value
                                              have complete : outcome (MatrixState.start state.field limits columns
                                                  reducers targets sugars independent) = outcome
                                                  (gatheredScan current output.state inverse gatherStats) := by
                                                simpa [current,scanState,scanning,preparedScan,hlimits,
                                                  ExceptT.run,gatherWork] using normalization
                                              let gathering := gatheredScan current output.state inverse gatherStats
                                              have gatheringGeometry := normalization_geometry current output.state
                                                inverse gatherStats rfl geometry bounds.1 bounds.2.1 bounds.2.2 leading
                                              have contract := nativeGather_spec gathering
                                                (by simp [gathering,gatheredScan]) gatheringGeometry
                                                (by simp [gathering,gatheredScan])
                                                (by simp [gathering,gatheredScan])
                                              have post := triple_post _ gathering.stats _ contract
                                              simp only [ExceptT.run,gatherWork]
                                              mvcgen
                                              simp only [Matrix.Work.pre]
                                              cases hg : (nativeGather state.field limits output.state.dense
                                                  (output.state.leading-1) output.state.last inverse).run gatherStats with
                                              | mk result finalStats =>
                                                simp only [ExceptT.run] at hg
                                                cases result with
                                                | error error =>
                                                  have failed : outcome gathering = (.error error,finalStats) := by
                                                    simpa [gathering,gatheredScan,current,scanState,scanning,
                                                      preparedScan,hlimits,ExceptT.run,hg] using post
                                                  simpa [ExceptT.run,hg,independentRow] using complete.trans failed
                                                | ok result =>
                                                  have returned : ∃ quanta,
                                                      (gatheredState gathering result.1 result.2 quanta finalStats).geometry ∧
                                                      outcome (gatheredState gathering result.1 result.2 quanta finalStats) =
                                                        outcome gathering := by
                                                    simpa [gathering,gatheredScan,current,scanState,scanning,
                                                      preparedScan,hlimits,ExceptT.run,hg] using post
                                                  rcases returned with ⟨remaining,completedGeometry,same⟩
                                                  have completed := same.trans complete.symm
                                                  simp only [ExceptT.run,hg]
                                                  mvcgen
                                                  all_goals
                                                    refine ⟨htrace,gatheredState gathering result.1 result.2
                                                      remaining finalStats,?_⟩
                                                    simp_all [gatheredState,install_run,gathering,gatheredScan,
                                                      current,scanState,scanning,preparedScan,
                                                      MatrixState.State.identity,MatrixState.State.geometry,
                                                      MatrixState.isTarget,MatrixState.start]
                                                  all_goals grind

namespace Elimination

/-- Empty matrices complete successfully without any charged work, on every
platform, field and resource allowance. -/
theorem reference_empty (field : PrimeField) (limits : MatrixLimits) (independent : Bool) :
    reference field limits 0 #[] #[] #[] independent =
      ⟨.ok (⟨#[],0,#[]⟩,#[]),{}⟩ := by
  cases independent
  all_goals simp [reference,eliminate,Matrix.validateRows,Matrix.zerosWith_spec,Matrix.zeros,
    Matrix.work,Matrix.packedBytes,Matrix.charge,Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size,ExceptT.run,ExceptT.mk,ExceptT.pure,ExceptT.bind,
    ExceptT.bindCont,ExceptT.lift,StateT.bind,StateT.get,StateT.set,StateT.pure,Bind.bind,
    MonadState.get,MonadStateOf.get,MonadStateOf.set,liftM,MonadLiftT.monadLift,
    MonadLift.monadLift,getThe,StateT.map,Functor.map,Pure.pure,Id.run,modify,modifyGet,
    MonadStateOf.modifyGet]

/-- info: 'Hex.Groebner.Elimination.reference_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms reference_empty

end Elimination

namespace MatrixState

/-- Completing any new continuation gives the reference eliminator's exact
result and charged statistics, for every input and every budget. The statement
also covers malformed inputs and row-quantum exhaustion. -/
theorem finish_reference (field : PrimeField) (limits : MatrixLimits) (columns : Nat)
    (reducers targets : Array SparseRow) (sugars : Array Nat) (independent : Bool)
    (quantum : Nat) (native : Bool) :
    finishWith quantum (start field limits columns reducers targets sugars independent) native =
      let result := Elimination.reference field limits columns reducers targets sugars independent
      (result.result,result.stats) := by
  rw [finishWith_schedule _ quantum 64 native false (start_geometry _ _ _ _ _ _ _)]
  have post := triple_post _ {} _ (eliminate_spec field limits columns reducers targets sugars independent)
  cases hr : (eliminate field limits columns reducers targets false sugars true independent).run {} with
  | mk result stats =>
    simp only [ExceptT.run] at hr
    cases result <;> simpa [Elimination.reference,outcome,ExceptT.run,hr] using post

/-- info: 'Hex.Groebner.MatrixState.finish_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms finish_reference

end MatrixState

end Hex.Groebner
