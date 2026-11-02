/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import all HexGroebner.MatrixState
import all HexGroebner.MatrixStateProof
import all HexGroebner.EliminationOutcome
import all HexGroebner.EliminationWorkProof
import all HexGroebner.EliminationInputProof
import all HexGroebner.EliminationOrderProof
public import HexGroebner.EliminationInputProof
public import HexGroebner.EliminationOrderProof
public import Std.Do

public section

/-! Owning row invariants inspect private phase bodies. State construction
stays behind the executable API. -/

namespace Hex.Groebner

open Std.Do

private theorem triple_post (action : Matrix.Work α) (initial : MatrixStats)
    (post : Matrix.Work.Post α)
    (contract : Triple action (fun stats => ⌜stats = initial⌝) post) :
    match action.run initial with
    | (.ok value,stats) => (post.1 value stats).down
    | (.error error,stats) => (post.2.1 error stats).down := by
  rw [Triple.iff] at contract
  have result := contract initial rfl
  cases hr : action.run initial with
  | mk value stats =>
    change action initial = (value,stats) at hr
    cases value <;> simpa [Std.Do.WP.wp,ExceptT.run,StateT.run,Id.run,Pure.pure,hr] using result

private def atInput (base : MatrixState.State) (input : Nat) (dense slots : ByteArray)
    (pivots : Array Pivot) (nativePivots : Array Native.Scan.Pivot) (trace : Array RowOp)
    (remainders : Array RemainderRow) (rank : Nat) (stats : MatrixStats) : Prop :=
  trace = #[] ∧ ∃ state : MatrixState.State,
    state.identity = base.identity ∧ state.phase = .input ∧ state.geometry ∧
    state.input = input ∧ state.dense = dense ∧ state.slots = slots ∧
    state.pivots = pivots ∧ state.nativePivots = nativePivots ∧
    state.remainders = remainders ∧ state.rank = rank ∧ state.stats = stats ∧
    outcome state = outcome base

private theorem input_finish (base : MatrixState.State) (dense slots : ByteArray)
    (pivots : Array Pivot) (nativePivots : Array Native.Scan.Pivot) (trace : Array RowOp)
    (remainders : Array RemainderRow) (rank : Nat) (stats : MatrixStats)
    (hinput : atInput base (base.reducers.size+base.targets.size) dense slots pivots nativePivots
      trace remainders rank stats) :
    outcome base = if base.independent then (.ok (⟨#[],rank,trace⟩,remainders),stats)
    else match (Matrix.work base.limits base.columns).run stats with
      | (.error error,stats) => (.error error,stats)
      | (.ok _,stats) => (.ok (⟨orderedPivots base.columns slots pivots,rank,trace⟩,remainders),stats) := by
  rcases hinput with ⟨htrace,state,hframe,hphase,hgeometry,hinput,hdense,hslots,hpivots,
    hnative,hremainders,hrank,hstats,hsame⟩
  simp only [MatrixState.State.identity,Prod.mk.injEq] at hframe
  rcases hframe with ⟨hfield,hlimits,hcolumns,hreducers,htargets,hsugars,hindependent⟩
  have stop := input_end state hphase hgeometry (by rw [hinput,hreducers,htargets]; exact Nat.le_refl _)
  have geometry : { state with phase := .order }.geometry := by
    simpa only [MatrixState.State.geometry,hphase] using hgeometry
  have final := order_outcome { state with phase := .order } rfl geometry
  have result := hsame.symm.trans (stop.trans final)
  simp only [hlimits,hcolumns,hslots,hpivots,hremainders,hrank,hstats,hindependent,htrace]
    at result ⊢
  by_cases independent : base.independent = true
  all_goals simp only [independent,ite_true] at result ⊢
  · exact result
  · cases hw : (Matrix.work base.limits base.columns).run stats with
    | mk value finalStats =>
      cases value <;> simpa only [hw] using result

private theorem range_cursor (count : Nat) (pref suff : List Nat) (cur : Nat)
    (h : [:count].toList = pref ++ cur :: suff) : cur = pref.length ∧ pref.length < count := by
  have length := congrArg List.length h
  simp [Std.Legacy.Range.toList] at length
  have bound : pref.length < count := by omega
  have value := congrArg (fun xs => xs[pref.length]?) h
  simp only [Std.Legacy.Range.toList] at value
  simp only [Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one] at value
  rw [List.getElem?_range' bound,List.getElem?_append_right (Nat.le_refl _)] at value
  simp only [Nat.sub_self,List.getElem?_cons_zero,Nat.one_mul,Nat.zero_add,Option.some.injEq] at value
  exact ⟨value.symm,bound⟩


#print axioms input_finish
#print axioms range_cursor
#print axioms triple_post

end Hex.Groebner
