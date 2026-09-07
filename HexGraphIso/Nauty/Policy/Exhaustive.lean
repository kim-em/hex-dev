/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Trivial
import all HexGraphIso.Nauty.Policy.Trivial
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.Search

public section

namespace Hex.GraphIso.Nauty.Generic.Trivial

variable {n : Nat}

/-- One exhaustive node refines, installs a discrete leaf, or sweeps all
positions of the specification target. -/
theorem node_step (ctx : Ctx n) (inf tcLevel fuel level : Nat) (st : State n) :
    Generic.node false ctx inf tcLevel (fuel + 1) level st.frame.partition.numcells st =
      let ready := visit ctx level st.frame.partition.numcells st
      if discreteAt ready.frame.partition.ptn level n then
        (.unwind (level - 1) false, install ready)
      else
        let p := ready.frame.partition
        let t := specMaketargetcell ctx p.lab p.ptn level tcLevel
        let cell : VSet n := positions t.2.2
        let out := Generic.sweep false ctx inf tcLevel fuel (n + 1) level p.numcells t.1
          ((cell.nextElem none).getD 0) (cell.nextElem none) cell 0 ready
        match out.1 with
        | .done => (.unwind (level - 1) false, out.2.2)
        | exit => (exit, out.2.2) := by
  rw [Generic.node]
  unfold Generic.nodeStep
  dsimp only [policy, Policy.visit, Policy.compareCodes, Policy.chooseTarget,
    Policy.classify, Policy.leafExit, Policy.cheapCheck, Policy.afterSweep]
  cases hd : discreteAt (visit ctx level st.frame.partition.numcells st).frame.partition.ptn level n
  all_goals simp only [hd, Bool.false_eq_true, ite_false, ite_true]
  · simp only [show (Leaf.internal == Leaf.internal) = true from rfl, ite_true,
      Int.ofNat_eq_natCast, Int.toNat_natCast]
    let ready := visit ctx level st.frame.partition.numcells st
    let p := ready.frame.partition
    let t := specMaketargetcell ctx p.lab p.ptn level tcLevel
    let cell : VSet n := positions t.2.2
    generalize hs : Generic.sweep false ctx inf tcLevel fuel (n + 1) level p.numcells t.1
      ((cell.nextElem none).getD 0) (cell.nextElem none) cell 0 ready = out
    obtain ⟨exit, index, result⟩ := out
    cases exit <;> rfl
  · rfl

/-- An exhaustive sweep folds its child maxima in increasing target-offset
order. Child calls leave their saved parent available for recovery. -/
theorem sweep_fold {ctx : Ctx n} {inf tcLevel fuel level tc len : Nat}
    (st : State n) (key : Nat → Key n) (hlen : len ≤ n)
    (hnode : ∀ o, o < len → ∀ best,
      Generic.node false ctx inf tcLevel fuel (level + 1) (st.frame.partition.numcells + 1)
        (child level tc o { st with best }) =
      (.unwind level false,
        { visit ctx (level + 1) (st.frame.partition.numcells + 1)
          (child level tc o { st with best }) with best := some (incMax best (key o)) })) :
    ∀ cfuel o, o ≤ len → len - o ≤ cfuel → ∀ best tv1 index,
      Generic.sweep false ctx inf tcLevel fuel cfuel level st.frame.partition.numcells tc tv1
        (if o < len then some o else none) (positions len) index { st with best } =
      (.done, index, { st with best := ((List.range' o (len - o)).foldl
        (fun best o => some (incMax best (key o))) best) }) := by
  intro cfuel
  induction cfuel with
  | zero =>
    intro o ho hf best tv1 index
    have he : o = len := by omega
    subst o
    simp [Generic.sweep]
  | succ cfuel ih =>
    intro o ho hf best tv1 index
    by_cases hlt : o < len
    · rw [ite_eq_left hlt, Generic.sweep]
      unfold Generic.sweepStep
      dsimp only [policy, Policy.child, Policy.afterChildFirst, Policy.leaveChild,
        Policy.orbit, Policy.shortprune, Policy.longprune, Policy.recover]
      simp only [Bool.not_false, Bool.true_or, Bool.false_and, Bool.false_eq_true,
        ite_true, ite_false]
      rw [hnode o hlt best]
      simp only [Nat.lt_irrefl, Bool.false_eq_true, ite_false, ite_self, Id.run_pure]
      rw [recover_child ctx level tc o { st with best } (some (incMax best (key o))),
        next_positions hlen]
      simp only [VSet.scanStart]
      have hnext := ih (o + 1) (by omega) (by omega)
        (some (incMax best (key o))) tv1 index
      have hcount : len - o = (len - (o + 1)) + 1 := by omega
      rw [hcount, List.range'_succ, List.foldl_cons]
      exact hnext
    · have he : o = len := by omega
      subst o
      simp [Generic.sweep]

/-- With enough depth for every leaf, the never-pruning policy computes
the specification maximum and restores each node's refined frame. -/
theorem node_eq {ctx : Ctx n} {tcLevel fuel level : Nat} {p : RefineSt n}
    (h : Complete ctx tcLevel fuel level p) (st : State n)
    (hp : st.frame.partition = p) (inf : Nat) :
    Generic.node false ctx inf tcLevel fuel level p.numcells st =
      (.unwind (level - 1) false,
        { visit ctx level p.numcells st with best := some (incMax st.best
          (prefixKey st.frame.codes (specNode ctx tcLevel fuel level p.lab p.ptn p.active p.numcells))) }) := by
  induction h generalizing st with
  | @leaf fuel level p hd =>
    subst p
    rw [node_step]
    simp only [visit, hd, ite_true, specNode, install, prefixKey, List.append_assoc,
      List.singleton_append]
  | @branch fuel level p hd hbound hchild ih =>
    subst p
    let ready := visit ctx level st.frame.partition.numcells st
    let r := ready.frame.partition
    let t := specMaketargetcell ctx r.lab r.ptn level tcLevel
    let tail := fun o =>
      let p := (child level t.1 o ready).frame.partition
      specNode ctx tcLevel fuel (level + 1) p.lab p.ptn p.active p.numcells
    let key := fun o => prefixKey ready.frame.codes (tail o)
    have hpos : 0 < t.2.2 := Nat.succ_pos _
    change t.2.2 ≤ n at hbound
    have hnode : ∀ o, o < t.2.2 → ∀ best,
        Generic.node false ctx inf tcLevel fuel (level + 1) (ready.frame.partition.numcells + 1)
          (child level t.1 o { ready with best }) =
        (.unwind level false,
          { visit ctx (level + 1) (ready.frame.partition.numcells + 1)
            (child level t.1 o { ready with best }) with best := some (incMax best (key o)) }) := by
      intro o ho best
      have hi := ih o ho (child level t.1 o { ready with best }) rfl
      simpa only [child, visit, ready, r, t, key, tail, Nat.add_sub_cancel] using hi
    have hs := sweep_fold ready key hbound hnode (n + 1) 0 (by omega) (by omega) st.best 0 0
    have hcursor : (positions t.2.2 : VSet n).nextElem none = some 0 := by
      rw [next_positions hbound]
      exact ite_eq_left hpos
    have hnc : List.range t.2.2 ≠ [] := by
      intro he
      have hl := congrArg List.length he
      simp only [List.length_range, List.length_nil] at hl
      omega
    obtain ⟨o, os, hos⟩ := List.exists_cons_of_ne_nil hnc
    have hfold : (List.range t.2.2).foldl (fun best o => some (incMax best (key o))) st.best =
        some (incMax st.best (keysMax (key o) (os.map key))) := by
      rw [hos]
      exact foldl_incMax_cons (fun _ _ _ => rfl) st.best
    have hmax : prefixKey st.frame.codes
        (specNode ctx tcLevel (fuel + 1) level st.frame.partition.lab st.frame.partition.ptn
          st.frame.partition.active st.frame.partition.numcells) =
        keysMax (key o) (os.map key) := by
      rw [specNode, hd]
      change prefixKey st.frame.codes
        (match (List.range t.2.2).map tail with
        | [] => ⟨[], []⟩
        | c :: cs => ⟨r.longcode :: (keysMax c cs).codes, (keysMax c cs).rows⟩) = _
      rw [hos, List.map_cons]
      rw [prefixKey_cons, prefixKey_keysMax, List.map_map]
      rfl
    rw [node_step]
    change (if discreteAt r.ptn level n then (.unwind (level - 1) false, install ready) else
      let cell : VSet n := positions t.2.2
      let out := Generic.sweep false ctx inf tcLevel fuel (n + 1) level r.numcells t.1
        ((cell.nextElem none).getD 0) (cell.nextElem none) cell 0 ready
      match out.1 with
      | .done => (.unwind (level - 1) false, out.2.2)
      | exit => (exit, out.2.2)) = _
    rw [show discreteAt r.ptn level n = false from hd]
    simp only [Bool.false_eq_true, ite_false, hcursor, Option.getD_some]
    simp only [Nat.sub_zero, ← List.range_eq_range', hpos, ite_true] at hs
    have hready : { ready with best := st.best } = ready := rfl
    rw [hready] at hs
    rw [hs, hfold, hmax]

/-- A well-formed partition reaches every leaf within the usual
level-versus-fuel bound. Each individualization adds a closed boundary. -/
theorem complete {ctx : Ctx n} {tcLevel fuel level : Nat} {p : RefineSt n}
    (hok : NodeOk n level p.lab p.ptn p.active)
    (hbc : level ≤ bcount p.ptn level n) (hfuel : n + 1 ≤ level + fuel) :
    Complete ctx tcLevel fuel level p := by
  induction fuel generalizing level p with
  | zero =>
    have hb := bcount_le p.ptn level n
    omega
  | succ fuel ih =>
    let r := refine ctx level p.lab p.ptn p.active p.numcells
    have hr := refine_stOk (ctx := ctx) (active := p.active) (numcells := p.numcells)
      hok.labSize hok.labOk hok.ptnSize hok.ptnEnd
    have hvals : ∀ q : Nat, r.ptn[q]! ≤ level ∨ r.ptn[q]! = n + 2 := by
      intro q
      rcases ptn_refine_vals ctx level p.lab p.ptn p.active p.numcells q with he | he
      · change r.ptn[q]! = p.ptn[q]! at he
        rw [he]
        exact hok.vals q
      · change r.ptn[q]! = level at he
        exact Or.inl (Nat.le_of_eq he)
    have href := refine_refInv (ctx := ctx) (level := level) (active := p.active)
      (numcells := p.numcells) (by rw [hok.ptnSize]; omega)
      (by rw [hok.labSize, hok.ptnSize]) hok.ptnEnd
    cases hd : discreteAt r.ptn level n with
    | true => exact .leaf hd
    | false =>
      obtain ⟨cell, htc, hne, hend, hcell, hce⟩ := targetcell_facts (ctx := ctx)
        (tcLevel := tcLevel) r.lab hr.ptnSize hr.ptnEnd hd
      let t := specMaketargetcell ctx r.lab r.ptn level tcLevel
      have ht : t.1 = cell.1 := htc
      have hlen : t.2.2 = cell.2 + 1 - cell.1 := by
        change cellEnd r.ptn level (specTargetcell ctx r.lab r.ptn level tcLevel + 1) -
          specTargetcell ctx r.lab r.ptn level tcLevel + 1 = _
        rw [htc, hce]
        omega
      refine .branch hd (by change t.2.2 ≤ n; omega) ?_
      dsimp only
      intro o ho
      change o < t.2.2 at ho
      have hchild := childNodeOk (o := o) hr.labSize hr.labOk hr.ptnSize hr.ptnEnd
        hvals hcell (by omega) (by omega)
      have hcount : level + 1 ≤ bcount (r.ptn.set! cell.1 (level + 1)) (level + 1) n := by
        have hmono : bcount p.ptn level n ≤ bcount r.ptn level n := bcount_mono href.grow
        have hlevel : level ≤ n := Nat.le_trans hbc (bcount_le _ _ _)
        have hsplit := bcount_breakout (n := n) (nn := n) hvals (by omega : level + 1 < n + 2)
          (hcell.2.2.1 cell.1 (Nat.le_refl _) (by omega))
          (by omega) (by rw [hr.ptnSize]; omega)
        omega
      apply ih (p := (child level t.1 o ⟨⟨r, [], default⟩, [], none⟩).frame.partition)
      · simpa only [child, ht, r, breakout] using hchild
      · simpa only [child, ht, breakout] using hcount
      · omega

/-- Starting with no incumbent and no path prefix, exhaustive generic
search returns exactly the declarative subtree key with sufficient fuel. -/
theorem generic_trivial_eq_specNode {ctx : Ctx n} {tcLevel fuel level : Nat} {p : RefineSt n}
    (hok : NodeOk n level p.lab p.ptn p.active)
    (hbc : level ≤ bcount p.ptn level n) (hfuel : n + 1 ≤ level + fuel) (inf : Nat) :
    (Generic.node false ctx inf tcLevel fuel level p.numcells
      (⟨⟨p, [], default⟩, [], none⟩ : State n)).2.best =
      some (specNode ctx tcLevel fuel level p.lab p.ptn p.active p.numcells) := by
  rw [node_eq (complete hok hbc hfuel) _ rfl]
  rfl

end Hex.GraphIso.Nauty.Generic.Trivial
