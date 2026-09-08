/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Search.Budget
public import HexPermGroup.Search.Predicate

public section

namespace Hex.PermGroup.Search

variable {budget : Budget}

abbrev CheckedBool (expected : Bool) := {value : Bool // value = expected}

/-- Charge a membership query before sifting through its complete chain. -/
@[expose] def Meter.sift (m : Meter budget) (G : Group n) (p : Perm n) :
    Measured budget (CheckedBool (G.contains p)) :=
  match m.spend .sifts 1 with
  | .error failure => .exhausted failure
  | .ok meter => .ok ⟨G.contains p, rfl⟩ meter

/-- Check a finite generator family, stopping at the first failed membership
query or before the next query when the sift allowance is exhausted. -/
@[expose] def Meter.allSifts (m : Meter budget) (G : Group n) (size : Nat) (values : Fin size → Perm n) :
    Measured budget (CheckedBool (decide (∀ i : Fin size, G.contains (values i) = true))) :=
  let run := (Trials.range size).scan (fun i => !G.contains (values i)) 0 (m.available .sifts)
  let meter := m.charge .sifts run.used run.bounded
  match hr : run.result with
  | .found i _ hi _ =>
    .ok ⟨false, by
      apply Eq.symm
      apply decide_eq_false
      intro h
      let j : Fin size := ⟨i.val, i.isLt⟩
      have hj : (Trials.range size).get i = j := rfl
      rw [hj] at hi
      have he := h j
      simp only [he, Bool.not_true, Bool.false_eq_true] at hi⟩ meter
  | .clear checked =>
    .ok ⟨true, by
      apply Eq.symm
      apply decide_eq_true
      intro i
      let j : Fin (Trials.range size).size := ⟨i.val, i.isLt⟩
      have hj : (Trials.range size).get j = i := Fin.ext rfl
      have he := checked j (Nat.zero_le _)
      rw [hj] at he
      simpa only [Bool.not_eq_false'] using he⟩ meter
  | .incomplete =>
    .exhausted ⟨meter, .sifts, 1, by
      change (m.charge .sifts run.used run.bounded).available .sifts < 1
      rw [Meter.available_charge, run.depleted hr]
      simp⟩

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
      rw [Meter.available_charge, run.depleted hr]
      simp⟩

end Hex.PermGroup.Search
