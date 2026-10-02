/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SortPartition
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse.Sort

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 800000

/-- The exact two pushes in the indirect sort, with the smaller fragment
at the top of the stack. Fragments of size at most one need no work. -/
@[expose] def children (start size left right : Nat) (rest : List (Nat × Nat)) : List (Nat × Nat) :=
  if left > right then
    let stack := if left > 1 then (start, left) :: rest else rest
    if right > 1 then (start + size - right, right) :: stack else stack
  else
    let stack := if right > 1 then (start + size - right, right) :: rest else rest
    if left > 1 then (start, left) :: stack else stack

/-- Total length of the pending segments. -/
@[expose] def weight (stack : List (Nat × Nat)) : Nat := (stack.map Prod.snd).sum

@[simp] theorem weight_nil : weight [] = 0 := rfl

@[simp] theorem weight_cons (p : Nat × Nat) (rest : List (Nat × Nat)) :
    weight (p :: rest) = p.2 + weight rest := by simp [weight]

theorem children_weight (start size left right : Nat) (rest : List (Nat × Nat)) :
    weight (children start size left right rest) ≤ left + right + weight rest := by
  unfold children
  split <;> split <;> split <;> simp only [weight_cons] <;> omega

theorem children_bounds (start size left right bound : Nat) (rest : List (Nat × Nat))
    (hb : start + size ≤ bound) (hl : left ≤ size) (hr : right ≤ size)
    (hs : ∀ p ∈ rest, 1 < p.2 ∧ p.1 + p.2 ≤ bound) :
    ∀ p ∈ children start size left right rest, 1 < p.2 ∧ p.1 + p.2 ≤ bound := by
  unfold children
  split <;> split <;> split <;> simp_all only [List.mem_cons, forall_eq_or_imp]
  all_goals grind

/-- Induction over the actual bounded work-stack loop. A property preserved
by its insertion and partition steps holds with an empty final stack: the
loop bound cannot truncate pending work on a valid input segment. -/
theorem indirect_induction (x y : Array Nat) (start len : Nat)
    (hb : start + len ≤ x.size) (P : Array Nat → List (Nat × Nat) → Prop)
    (hinit : P x (if len > 1 then [(start, len)] else []))
    (hins : ∀ a lo size rest, a.size = x.size → lo + size ≤ x.size → size < 11 →
      P a ((lo, size) :: rest) → P (insertion a y lo size) rest)
    (hpart : ∀ a lo size rest, a.size = x.size → lo + size ≤ x.size → 11 ≤ size →
      P a ((lo, size) :: rest) →
      P (partition a y lo size).1 (children lo size (partition a y lo size).2.1
        (partition a y lo size).2.2 rest)) :
    P (indirect x y start len) [] := by
  have hstep (a : Array Nat) (lo size : Nat) (rest : List (Nat × Nat)) (done : Nat)
      (has : a.size = x.size) (hbs : lo + size ≤ x.size) (hlarge : 11 ≤ size)
      (hp : P a ((lo, size) :: rest))
      (hrest : ∀ p ∈ rest, 1 < p.2 ∧ p.1 + p.2 ≤ x.size)
      (hw : size + weight rest + done ≤ len) :
      let r := partition a y lo size
      r.1.size = x.size ∧ P r.1 (children lo size r.2.1 r.2.2 rest) ∧
        (∀ p ∈ children lo size r.2.1 r.2.2 rest, 1 < p.2 ∧ p.1 + p.2 ≤ x.size) ∧
        weight (children lo size r.2.1 r.2.2 rest) + (done + 1) ≤ len := by
    have hr := (partition_proper a y lo size (by omega) (by omega)).1
    have hw' := children_weight lo size (partition a y lo size).2.1
      (partition a y lo size).2.2 rest
    exact ⟨(partition_size a y lo size).trans has, hpart a lo size rest has hbs hlarge hp,
      children_bounds _ _ _ _ _ _ hbs (by omega) (by omega) hrest, by omega⟩
  unfold indirect
  apply Id.of_wp_run_eq rfl (fun a : Array Nat => P a [])
  mvcgen invariants
  | inv1 => ⇓⟨cursor, s⟩ => ⌜
      s.1.size = x.size ∧ P s.1 s.2 ∧
      (∀ p ∈ s.2, 1 < p.2 ∧ p.1 + p.2 ≤ x.size) ∧
      (s.2 = [] ∨ weight s.2 + cursor.prefix.length ≤ len)⌝
  all_goals
    simp +zetaDelta only [Std.Legacy.Range.toList, Nat.add_sub_cancel, Nat.sub_zero,
      Nat.div_one, List.length_append, List.length_cons, List.length_nil,
      List.length_range', Nat.add_zero] at *
  all_goals
    try simp_all only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil, forall_const,
      List.cons_ne_nil, false_or, true_or, and_true, true_and, weight_cons,
      Nat.zero_add]
  case vc1.step.h_1 => simp
  case vc2.step.h_2.isTrue =>
    clear hstep hpart hins hinit
    grind only [insertion_size]
  case vc11.pre =>
    clear hstep hpart hins hinit
    by_cases hlen : len > 1 <;> simp_all [weight]
  case vc12.post.success =>
    rename_i hin
    rcases hin.2.2.2 with he | hw
    · simpa only [he] using hin.2.1
    · omega
  all_goals
    rename_i hin hr
    have hpnew := hpart _ _ _ _ hin.1 hin.2.2.1.1.2 (by omega) hin.2.1
    have hnew := hstep _ _ _ _ _ hin.1 hin.2.2.1.1.2 (by omega)
      hin.2.1 hin.2.2.1.2 hin.2.2.2
    clear hstep hpart hins hinit
    simp (disch := omega) only [children, ite_eq_left, ite_eq_right] at hpnew hnew
    try simp only [List.mem_cons, forall_eq_or_imp, weight_cons] at hnew
    grind only [weight_cons, List.mem_cons]

private theorem children_inside (lo size left right : Nat) (rest : List (Nat × Nat))
    (hl : left ≤ size) (hr : right ≤ size) :
    ∀ p ∈ children lo size left right rest,
      p ∈ rest ∨ lo ≤ p.1 ∧ p.1 + p.2 ≤ lo + size := by
  unfold children
  split <;> split <;> split
  all_goals
    intro p hp
    simp only [List.mem_cons] at hp
    grind

/-- The full indirect sort changes only entries in the requested segment. -/
theorem indirect_outside (x y : Array Nat) (start len q : Nat)
    (hb : start + len ≤ x.size) (hq : q < start ∨ start + len ≤ q) :
    (indirect x y start len)[q]! = x[q]! := by
  let P := fun (a : Array Nat) (stack : List (Nat × Nat)) =>
    a[q]! = x[q]! ∧ ∀ p ∈ stack, start ≤ p.1 ∧ p.1 + p.2 ≤ start + len
  have h := indirect_induction x y start len hb P ?_ ?_ ?_
  · exact h.1
  · dsimp [P]
    split <;> simp_all
  · intro a lo size rest has hbs hsmall hp
    have hseg := hp.2 (lo, size) (by simp)
    refine ⟨(insertion_outside a y lo size q (by omega)).trans hp.1, ?_⟩
    intro p hm
    exact hp.2 p (by simp [hm])
  · intro a lo size rest has hbs hlarge hp
    have hseg := hp.2 (lo, size) (by simp)
    have hr := partition_proper a y lo size (by omega) (by omega)
    refine ⟨(hr.2 q (by omega)).trans hp.1, ?_⟩
    intro p hm
    rcases children_inside lo size _ _ rest (by omega) (by omega) p hm with hmem | hsub
    · exact hp.2 p (by simp [hmem])
    · constructor <;> omega

theorem extract_eq {a b : Array Nat} (hs : a.size = b.size) (lo hi : Nat)
    (he : ∀ q, lo ≤ q → q < hi → a[q]! = b[q]!) :
    a.extract lo hi = b.extract lo hi := by
  apply Array.ext
  · simp [hs]
  · intro i hi' hj'
    simp only [Array.getElem_extract]
    have hb : lo + i < a.size := by simp only [Array.size_extract] at hi'; omega
    have h := he (lo + i) (by omega) (by simp only [Array.size_extract] at hi'; omega)
    rwa [getElem!_pos a (lo + i) hb, getElem!_pos b (lo + i) (by omega)] at h

theorem split_three (a : Array Nat) (lo hi bound : Nat)
    (hlo : lo ≤ hi) (hhi : hi ≤ bound) (ha : a.size = bound) :
    (a.extract 0 lo ++ a.extract lo hi) ++ a.extract hi bound = a := by
  simp only [Array.extract_append_extract, Nat.zero_min,
    Nat.max_eq_right hlo, Nat.max_eq_right hhi]
  rw [← ha, Array.extract_size]

/-- Permutation preservation holds for the segment itself, with the
unchanged prefix and suffix cancelled from the whole-array permutation. -/
theorem indirect_segment (x y : Array Nat) (start len : Nat)
    (hb : start + len ≤ x.size) :
    ((indirect x y start len).extract start (start + len)).toList.Perm
      (x.extract start (start + len)).toList := by
  have hs := indirect_size x y start len
  have hp := indirect_perm x y start len hb
  have hpre := extract_eq hs 0 start (fun q _ hq => indirect_outside x y start len q hb (.inl hq))
  have hpost := extract_eq hs (start + len) x.size
    (fun q hq _ => indirect_outside x y start len q hb (.inr hq))
  have ha := congrArg Array.toList
    (split_three (indirect x y start len) start (start + len) x.size (by omega) hb hs).symm
  have hx := congrArg Array.toList (split_three x start (start + len) x.size (by omega) hb rfl).symm
  simp only [Array.toList_append] at ha hx
  rw [ha, hx, hpre, hpost] at hp
  exact (List.perm_append_left_iff _).mp ((List.perm_append_right_iff _).mp hp)

end Hex.GraphIso.Nauty.Sparse.Sort
