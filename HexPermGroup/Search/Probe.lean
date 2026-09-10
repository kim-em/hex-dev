/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Search.Budget
public import HexPermGroup.Search.Predicate
public import HexPermGroup.Chain.Bounded

public section

namespace Hex.PermGroup.Search

variable {budget : Budget}

abbrev CheckedBool (expected : Bool) := {value : Bool // value = expected}

/-- Charge each visited level and permutation allocation in a membership query. -/
@[expose] def _root_.Hex.PermGroup.Execution.Meter.sift (m : Meter budget) (G : Group n) (p : Perm n) :
    Measured budget (CheckedBool (G.contains p)) := m.execute do
  let result ← G.chain.siftWith 0 p
  return ⟨result.val.accepted, congrArg SiftResult.accepted result.property⟩

/-- Query a finite family without materializing it. The caller supplies the
permutation-image reservation needed to evaluate one entry of the family. -/
@[expose] def siftFrom (G : Group n) (size : Nat) (values : Fin size → Perm n)
    (imageCost start : Nat) : Execution.Run budget
      (CheckedBool (decide (∀ i : Fin size, start ≤ i.val → G.contains (values i) = true))) := do
  if hi : start < size then
    Execution.reserve .images imageCost
    let result ← G.chain.siftWith 0 (values ⟨start, hi⟩)
    have he : result.val.accepted = G.contains (values ⟨start, hi⟩) :=
      congrArg SiftResult.accepted result.property
    if hm : result.val.accepted = true then
      let tail ← siftFrom G size values imageCost (start + 1)
      return ⟨tail.val, by
        rw [tail.property]
        apply decide_eq_decide.mpr
        constructor
        · intro h i hstart
          by_cases hs : i.val = start
          · have hj : i = ⟨start, hi⟩ := Fin.ext hs
            simpa only [hj] using he.symm.trans hm
          · exact h i (by omega)
        · intro h i hs
          exact h i (by omega)⟩
    else
      return ⟨false, by
        symm
        apply decide_eq_false
        intro h
        exact hm (he.trans (h ⟨start, hi⟩ (Nat.le_refl _)))⟩
  else
    return ⟨true, by
      symm
      apply decide_eq_true
      intro i hs
      omega⟩
termination_by size - start

/-- Check a finite generator family, stopping at its first failed membership
query or exhausted reservation. Image costs cover any generated query values. -/
@[expose] def _root_.Hex.PermGroup.Execution.Meter.allSifts (m : Meter budget) (G : Group n)
    (size : Nat) (values : Fin size → Perm n) (imageCost : Nat := 0) :
    Measured budget (CheckedBool (decide (∀ i : Fin size, G.contains (values i) = true))) :=
  m.execute do
    let result ← siftFrom G size values imageCost 0
    return ⟨result.val, by simpa only [Nat.zero_le, forall_const] using result.property⟩

variable {G : Group n}

/-- Coverage requires both the prefix and every suffix generator. A partial
family check cannot certify coverage or its negation. -/
@[expose] def Node.coveredWith (t : Node G) (K : Group n) (m : Meter budget) :
    Measured budget (CheckedBool (t.covered K)) :=
  match m.sift K t.rep.val with
  | .exhausted failure => .exhausted failure
  | .ok value meter =>
    if hv : value.val = true then
      match meter.allSifts K t.suffix.generators.size
          (fun i : Fin t.suffix.generators.size => t.suffix.generators[i.val]'i.isLt) with
      | .exhausted failure => .exhausted failure
      | .ok result meter => .ok ⟨result.val, by
          have he : K.contains t.rep.val = true := value.property.symm.trans hv
          simpa only [Node.covered, he, Bool.true_and] using result.property⟩ meter
    else .ok ⟨false, by
      have he : K.contains t.rep.val = false := value.property.symm.trans (Bool.eq_false_iff.mpr hv)
      simp only [Node.covered, he, Bool.false_and]⟩ meter

/-- A budgeted leaf evaluator retains the exact executable predicate. The
standard evaluators count its membership queries in the shared meter. -/
abbrev Evaluator (test : Perm n → Bool) (budget : Budget) :=
  (p : Perm n) → Meter budget → Measured budget (CheckedBool (test p))

abbrev Tester (P : Predicate n) (budget : Budget) := Evaluator P.test budget

@[expose] def Evaluator.pure (test : Perm n → Bool) : Evaluator test budget :=
  fun p meter => .ok ⟨test p, rfl⟩ meter

/-- Predicates containing no membership queries can use this evaluator. -/
@[expose] def Tester.pure (P : Predicate n) : Tester P budget :=
  Evaluator.pure P.test

@[expose] def Tester.subgroup (H : Group n) : Tester (Predicate.subgroup H) budget :=
  fun p meter => meter.sift H p

/-- Each attempted pruning reason is charged separately. Completing the scan
without finding a reason allows traversal to continue; exhausting it does not. -/
@[expose] def Pruner.refineWith {test : Perm n → Bool} (C : Pruner G test) (t : Node G) (m : Meter budget) :
    Measured budget (Option {r : C.Reason // C.reject t r = true}) :=
  let run := C.findWith t (m.available .refinements)
  let meter := m.charge .refinements run.used run.bounded
  match hr : run.result with
  | .found i _ hi _ => .ok (some ⟨(C.trials t).get i, hi⟩) meter
  | .clear _ => .ok none meter
  | .incomplete => .exhausted ⟨meter, .refinements, 1, by
      change (m.charge .refinements run.used run.bounded).available .refinements < 1
      rw [_root_.Hex.PermGroup.Execution.Meter.available_charge, run.depleted hr]
      simp⟩

end Hex.PermGroup.Search
