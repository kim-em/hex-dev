/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SortBlocks
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse.Sort

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 800000

/-- The scans exhaust their unclassified interval before the loop bound.
The final block swaps then separate strictly smaller, equal, and strictly
larger keys at exactly the two fragment boundaries returned by the code. -/
theorem partition_order (x y : Array Nat) (start len : Nat)
    (hb : start + len ≤ x.size) (hl : 0 < len) :
    Separated (partition x y start len).1 y start (start + len) (pivot x y start len)
      (start + (partition x y start len).2.1)
      (start + len - (partition x y start len).2.2) := by
  unfold partition
  apply Id.of_wp_run_eq rfl (fun r : Array Nat × Nat × Nat =>
    Separated r.1 y start (start + len) (pivot x y start len)
      (start + r.2.1) (start + len - r.2.2))
  mvcgen invariants
  | inv1 => ⇓⟨cursor, s⟩ => ⌜
      Cuts s.1 y start (start + len) (pivot x y start len)
        s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2 ∧
      Store s.1 x y start (start + len) (pivot x y start len) ∧
      (s.2.2.2.1 - s.2.2.1 + cursor.prefix.length ≤ len ∨
        (cursor.suffix = [] ∧ s.2.2.1 = s.2.2.2.1))⌝
  | inv2 pref it suff hr outer xs pair a pair2 b pair3 c d hout => ⇓⟨cursor, s⟩ => ⌜
      Cuts s.1 y start (start + len) (pivot x y start len) s.2.1 s.2.2 c d ∧
      Store s.1 x y start (start + len) (pivot x y start len) ∧
      (start + cursor.prefix.length ≤ s.2.2 ∨ (cursor.suffix = [] ∧
        (s.2.2 = c ∨ pivot x y start len < y[s.1[s.2.2]!]!))) ∧
      c - s.2.2 + pref.length ≤ len⌝
  | inv3 pref it suff hr outer xs pair a0 pair2 b0 pair3 c d hout r xr rest a b hleft =>
      ⇓⟨cursor, s⟩ => ⌜
      Cuts s.1 y start (start + len) (pivot x y start len) a b s.2.1 s.2.2 ∧
      Store s.1 x y start (start + len) (pivot x y start len) ∧
      (b = s.2.1 ∨ pivot x y start len < y[s.1[b]!]!) ∧
      (s.2.1 + cursor.prefix.length ≤ start + len ∨ (cursor.suffix = [] ∧
        (b = s.2.1 ∨ y[s.1[s.2.1 - 1]!]! < pivot x y start len))) ∧
      s.2.1 - b + pref.length ≤ len⌝
  | inv4 outer xs pair a pair2 b pair3 c d ba dc left hout => ⇓⟨cursor, out⟩ => ⌜
      Blocks out xs start (b - left) cursor.prefix.length⌝
  | inv5 outer xs pair a pair2 b pair3 c d ba dc left hout middle right hmid =>
      ⇓⟨cursor, out⟩ => ⌜Blocks out middle b (start + len - right) cursor.prefix.length⌝
  all_goals
    simp +zetaDelta only [Std.Legacy.Range.toList, Nat.add_sub_cancel, Nat.sub_zero,
      Nat.div_one, List.length_append, List.length_cons, List.length_nil,
      List.length_range', Nat.add_zero] at *
  all_goals
    try simp_all only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq,
      List.cons_ne_nil, false_and, or_false, true_and, Nat.zero_add]
  case vc11.pre =>
    refine ⟨Cuts.initial _ _ _ _ _ (by omega), ⟨rfl, fun _ _ => rfl, ?_⟩, Or.inl (by omega)⟩
    obtain ⟨i, hi, he⟩ := pivot_mem x y start len hl
    exact ⟨start + i, by omega, by omega, he.symm⟩
  case vc1.step.isTrue =>
    rename_i hguard hin hr hs
    have hbounds := hin.1.bounds
    simp only [and_true]
    omega
  case vc2.step.isFalse.isTrue =>
    rename_i hguard heq hin hr hs
    have hbounds := hin.1.bounds
    have hsize := hin.2.1.size_eq
    refine ⟨hin.1.left_eq_step (by omega) (by omega) heq, ?_,
      Or.inl (by omega), by omega⟩
    apply hin.2.1.swap <;> omega
  case vc6.step.isFalse.isTrue =>
    rename_i hguard heq hin hr hs hleft
    have hbounds := hin.1.bounds
    have hsize := hin.2.1.size_eq
    refine ⟨hin.1.right_eq_step (by omega) (by omega) heq, ?_, ?_,
      Or.inl (by omega), by omega⟩
    · apply hin.2.1.swap <;> omega
    · exact right_stop _ _ _ _ _ _ (by omega) (by omega) (by omega) hin.2.2.1
  case vc10.step.post.success.post.success.isFalse =>
    rename_i hguard next b c hr hleft hin
    have hbounds := hin.1.bounds
    have hsize := hin.2.1.size_eq
    refine ⟨hin.1.cross (by omega) (by omega) (by omega) (by omega), ?_, Or.inl (by omega)⟩
    apply hin.2.1.swap <;> omega
  all_goals
    try grind only [Cuts.bounds, Store.size_eq, Cuts.left_lt_step, Cuts.right_gt_step,
      List.mem_of_range'_eq_append_cons, List.mem_range'_1]
  case vc4.step.pre =>
    rename_i hin hr
    have hbounds := hin.1.bounds
    exact ⟨Or.inl (by omega), trivial⟩
  case vc5.step.isTrue =>
    rename_i hguard hin hr hs hleft
    have hbounds := hin.1.bounds
    simp only [and_true]
    omega
  case vc8.step.post.success.pre =>
    rename_i hr hin
    have hbounds := hin.1.bounds
    exact ⟨by omega, Or.inl (by omega), trivial⟩
  case vc9.step.post.success.post.success.isTrue =>
    rename_i hin
    have hbounds := hin.1.bounds
    omega
  case vc13.post.success.pre | vc15.post.success.post.success.pre =>
    exact Blocks.initial _ _ _
  case vc12.step =>
    rename_i r xs pair a pair2 b pair3 c d ba dc left pref i suff out next hin hr hout
    have hbounds := hout.1.bounds
    have hsize := hout.2.1.size_eq
    have hi := List.eq_of_range'_eq_append_cons hr
    have hi' := List.mem_of_range'_eq_append_cons hr
    simp only [Nat.zero_add, Nat.one_mul, List.mem_range'_1] at hi hi'
    simpa only [← hi] using hin.step
      (count := min (r.2.1 - start) (r.2.2.1 - r.2.1)) (by omega) (by omega) (by omega)
  case vc14.step =>
    rename_i r xs pair a pair2 b pair3 c d ba dc left middle right pref i suff out next
      hin hmid hr hout
    have hbounds := hout.1.bounds
    have hsize := hout.2.1.size_eq
    have hmidsize := hmid.1
    have hi := List.eq_of_range'_eq_append_cons hr
    have hi' := List.mem_of_range'_eq_append_cons hr
    simp only [Nat.zero_add, Nat.one_mul, List.mem_range'_1] at hi hi'
    have hmeet := hout.2.2
    simpa only [← hi] using hin.step
      (count := min (r.2.2.2.2 - r.2.2.2.1) (start + len - r.2.2.2.2))
      (by omega) (by omega) (by omega)
  case vc16.post.success.post.success.post.success =>
    rename_i hmid hfinal hout
    rcases hout.2.2 with hbad | hmeet
    · omega
    have hcuts := hout.1
    rw [← hmeet] at hcuts hfinal ⊢
    have hleft := hcuts.left_block hmid
    exact hleft.1.right_block hleft.2 hfinal

end Hex.GraphIso.Nauty.Sparse.Sort
