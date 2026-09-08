/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Search.Build
public import HexPermGroup.Search.Image
public import HexPermGroup.Action

public section

namespace Hex.PermGroup.Search

namespace Sets

/-- Forward images preserve the prescribed source and target membership colors. -/
@[expose] def test (A B : Vector Bool n) (p : Perm n) : Bool :=
  decide (∀ x : Fin n, A.get x = B.get (p.get x))

theorem test_action (G : Group n) (A B : Vector Bool n) (p : Element G) :
    test A B p.val = true ↔ (Action.subsets G).act p A = B := by
  constructor
  · intro h
    apply Vector.ext
    intro i hi
    simpa [Action.subsets, Vector.get] using (of_decide_eq_true h) (p.val.inv.get ⟨i, hi⟩)
  · intro h
    apply decide_eq_true
    intro x
    have he := congrArg (fun v : Vector Bool n => v.get (p.val.get x)) h
    simpa only [Action.subsets_apply] using he

end Sets

@[expose] def Predicate.setStabilizer (A : Vector Bool n) : Predicate n where
  test := Sets.test A A
  id := by simp [Sets.test]
  comp p q hp hq := by
    apply decide_eq_true
    intro x
    simpa only [Perm.get_comp] using ((of_decide_eq_true hq) x).trans ((of_decide_eq_true hp) (q.get x))
  inv p hp := by
    apply decide_eq_true
    intro x
    simpa only [Perm.get_inv_get] using ((of_decide_eq_true hp) (p.inv.get x)).symm

namespace Sets

variable {G : Group n}

/-- Counts are taken over a suffix orbit and its prefix image. A completion
only permutes that orbit, so it cannot repair a mismatch between the counts. -/
theorem orbit_count (A B : Vector Bool n) (t : Node G) (p : Perm n) (hp : t.Contains p)
    (h : test A B p = true) (x : Fin n) :
    (t.orbit x).toList.countP A.get = (t.orbit x).toList.countP (fun y => B.get (t.rep.val.get y)) := by
  have he := (t.orbit_perm hp x).countP_eq (fun y => B.get (t.rep.val.get y))
  simp only [List.countP_map, Function.comp_def, Perm.get_comp, Perm.get_inv_get] at he
  have hf : (fun y => B.get (p.get y)) = A.get := funext (fun y => ((of_decide_eq_true h) y).symm)
  rw [hf] at he
  exact he

inductive Reason (n : Nat) where
  | color (x : Fin n)
  | orbit (x : Fin n)

@[expose] def reject (A B : Vector Bool n) (t : Node G) : Reason n → Bool
  | .color x => decide (x.val < t.base) && decide (A.get x ≠ B.get (t.rep.val.get x))
  | .orbit x => decide ((t.orbit x).toList.countP A.get ≠
      (t.orbit x).toList.countP (fun y => B.get (t.rep.val.get y)))

theorem reject_sound (A B : Vector Bool n) (t : Node G) (r : Reason n) (hr : reject A B t r = true)
    (p : Perm n) (hp : t.Contains p) : test A B p = false := by
  apply Bool.eq_false_iff.mpr
  intro hP
  cases r with
  | color x =>
    simp only [reject, Bool.and_eq_true, decide_eq_true_eq] at hr
    apply hr.2
    simpa only [t.agrees hp x hr.1] using (of_decide_eq_true hP) x
  | orbit x =>
    exact (of_decide_eq_true hr) (orbit_count A B t p hp hP x)

/-- Assigned colors are tested before orbit counts, in source-point order,
without allocating all candidate reasons before testing the first. -/
@[expose] def trials (n : Nat) : Trials (Reason n) :=
  ((Trials.range n).map Reason.color).append ((Trials.range n).map Reason.orbit)

@[expose] def find (A B : Vector Bool n) (t : Node G) : Option (Reason n) :=
  (trials n).find (reject A B t)

theorem find_checked (A B : Vector Bool n) (t : Node G) (r : Reason n) (h : find A B t = some r) :
    reject A B t r = true := (trials n).find_checked (reject A B t) r h

@[expose] def constraint (G : Group n) (A : Vector Bool n) : Constraint G (Predicate.setStabilizer A) where
  Reason := Reason n
  reject := reject A A
  sound := reject_sound A A
  trials _ := trials n

end Sets

end Hex.PermGroup.Search

namespace Hex.PermGroup.Group

@[expose] def setStabilizerSearch (G : Group n) (A : Vector Bool n) : Search.Solution (Search.Sets.constraint G A) :=
  Search.solve (Search.Sets.constraint G A)

@[expose] def setStabilizer (G : Group n) (A : Vector Bool n) : Group n := (G.setStabilizerSearch A).group

theorem mem_setStabilizer (G : Group n) (A : Vector Bool n) (p : Perm n) :
    Generated (G.setStabilizer A).generators p ↔
      Generated G.generators p ∧ ∀ x : Fin n, A.get x = A.get (p.get x) := by
  rw [setStabilizer, Search.Solution.spec]
  exact and_congr_right (fun _ => decide_eq_true_iff)

/-- Both empty and full subsets are stabilized by the whole group. -/
theorem setStabilizer_constant (G : Group n) (value : Bool) :
    SameGroup (G.setStabilizer (Vector.replicate n value)) G := by
  intro p
  rw [mem_setStabilizer]
  simp [Vector.get]

end Hex.PermGroup.Group
