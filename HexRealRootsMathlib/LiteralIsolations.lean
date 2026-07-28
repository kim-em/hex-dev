/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealRootsMathlib.LiteralChain

public section

/-!
# Isolation semantics for literal root counts

This module separates real-root isolation semantics from the executable
`Hex.sturmCount` and `Hex.rootCount` functions. A `LiteralIsolation` stores an
interval whose supplied count is one; a `LiteralIsolations` stores an ordered
array of those intervals whose size is a supplied total count. Semantic
exactness of the two supplied counts is an explicit hypothesis of the
theorems below.

This is the interface used by certificate checkers that replay a literal
Sturm chain: the checker may define its counts from that chain without first
identifying it with `Hex.ZPoly.sturmChain`.
-/

namespace HexRealRootsMathlib

open Polynomial

noncomputable section

/-- One interval certified by an externally supplied integer root count. -/
structure LiteralIsolation (count : Hex.DyadicInterval → Int) where
  /-- The half-open interval `(lower, upper]`. -/
  interval : Hex.DyadicInterval
  /-- The supplied count says that the interval contains one root. -/
  count_one : count interval = 1

/-- An ordered, complete array of intervals certified by externally supplied
interval and total root counts. -/
structure LiteralIsolations (count : Hex.DyadicInterval → Int) (total : Int) where
  /-- The count-one intervals. -/
  isolations : Array (LiteralIsolation count)
  /-- Earlier half-open intervals end no later than later intervals begin. -/
  ordered : ∀ i j : Fin isolations.size, i < j →
    isolations[i].interval.upper ≤ isolations[j].interval.lower
  /-- The supplied total count agrees with the number of intervals. -/
  complete : total = isolations.size

/-- A literal count of one denotes exactly one real root in the interval.

No squarefreeness hypothesis is needed locally: the exact multiset count of
the interval is already one. Nonzeroness is needed to pass between `IsRoot`
and membership in `Polynomial.roots`. -/
theorem LiteralIsolation.exists_unique_root {p : Hex.ZPoly}
    {count : Hex.DyadicInterval → Int} (hp : p ≠ 0)
    (iso : LiteralIsolation count)
    (hcount : count iso.interval = (Literal.rootsIn (toPolyℝ p) iso.interval).card) :
    ∃! r : ℝ, (toPolyℝ p).IsRoot r ∧ Literal.InInterval iso.interval r := by
  classical
  have hP : toPolyℝ p ≠ 0 := fun h => hp (toPolyℝ_eq_zero_iff.mp h)
  have hcardZ : ((Literal.rootsIn (toPolyℝ p) iso.interval).card : Int) = 1 := by
    rw [← hcount]
    exact iso.count_one
  have hcard : (Literal.rootsIn (toPolyℝ p) iso.interval).card = 1 := by
    exact_mod_cast hcardZ
  obtain ⟨r, hr⟩ := Multiset.card_eq_one.mp hcard
  have hrmem : r ∈ Literal.rootsIn (toPolyℝ p) iso.interval := by
    rw [hr]
    exact Multiset.mem_singleton_self r
  simp only [Literal.rootsIn, Multiset.mem_filter] at hrmem
  refine ⟨r, ⟨(Polynomial.mem_roots'.mp hrmem.1).2, hrmem.2⟩, ?_⟩
  rintro y ⟨hyroot, hyI⟩
  have hymem : y ∈ Literal.rootsIn (toPolyℝ p) iso.interval := by
    simp only [Literal.rootsIn, Multiset.mem_filter]
    exact ⟨Polynomial.mem_roots'.mpr ⟨hP, hyroot⟩, hyI⟩
  rw [hr, Multiset.mem_singleton] at hymem
  exact hymem

/-- An ordered complete array of literal count-one intervals captures every
real root at exactly one array index.

Squarefreeness is used only to show that the root multiset has no duplicate
elements, so equality of the supplied total count with `roots.card` measures
the number of distinct roots. -/
theorem LiteralIsolations.isolates {p : Hex.ZPoly}
    {count : Hex.DyadicInterval → Int} {total : Int} (hp : p ≠ 0)
    (hsf : Squarefree (toPolyℝ p)) (out : LiteralIsolations count total)
    (hcount : ∀ i : Fin out.isolations.size,
      count out.isolations[i].interval =
        (Literal.rootsIn (toPolyℝ p) out.isolations[i].interval).card)
    (htotal : total = ((toPolyℝ p).roots.card : Int)) :
    ∀ r : ℝ, (toPolyℝ p).IsRoot r →
      ∃! i : Fin out.isolations.size,
        Literal.InInterval out.isolations[i].interval r := by
  classical
  have hP : toPolyℝ p ≠ 0 := fun h => hp (toPolyℝ_eq_zero_iff.mp h)
  have hsep : (toPolyℝ p).Separable :=
    PerfectField.separable_iff_squarefree.mpr hsf
  have hnodup : (toPolyℝ p).roots.Nodup := nodup_roots hsep
  have H : ∀ i : Fin out.isolations.size, ∃ y : ℝ,
      ((toPolyℝ p).IsRoot y ∧ Literal.InInterval out.isolations[i].interval y) ∧
        ∀ z, ((toPolyℝ p).IsRoot z ∧
          Literal.InInterval out.isolations[i].interval z) → z = y :=
    fun i => LiteralIsolation.exists_unique_root hp out.isolations[i]
      (hcount i)
  choose theRoot hroot huniq using H
  have hmono : ∀ i j : Fin out.isolations.size, i < j → theRoot i < theRoot j := by
    intro i j hij
    have hord := out.ordered i j hij
    have hi : Dyadic.toReal out.isolations[i].interval.lower < theRoot i ∧
        theRoot i ≤ Dyadic.toReal out.isolations[i].interval.upper := by
      simpa only [Literal.InInterval] using (hroot i).2
    have hj : Dyadic.toReal out.isolations[j].interval.lower < theRoot j ∧
        theRoot j ≤ Dyadic.toReal out.isolations[j].interval.upper := by
      simpa only [Literal.InInterval] using (hroot j).2
    calc
      theRoot i ≤ Dyadic.toReal out.isolations[i].interval.upper := hi.2
      _ ≤ Dyadic.toReal out.isolations[j].interval.lower := toReal_le_toReal hord
      _ < theRoot j := hj.1
  have hinj : Function.Injective theRoot := by
    intro i j hij
    rcases lt_trichotomy i j with hlt | heq | hgt
    · exact absurd hij (ne_of_lt (hmono i j hlt))
    · exact heq
    · exact absurd hij.symm (ne_of_lt (hmono j i hgt))
  let rootSet := (toPolyℝ p).roots.toFinset
  have hmem : ∀ i, theRoot i ∈ rootSet := fun i =>
    Multiset.mem_toFinset.mpr (Polynomial.mem_roots'.mpr ⟨hP, (hroot i).1⟩)
  have hcardZ : (rootSet.card : Int) = out.isolations.size := by
    rw [show rootSet.card = (toPolyℝ p).roots.card by
      exact Multiset.toFinset_card_of_nodup hnodup]
    exact htotal.symm.trans out.complete
  have hcard : rootSet.card = out.isolations.size := by
    exact_mod_cast hcardZ
  have himage : Finset.image theRoot Finset.univ = rootSet := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact hmem i
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ,
        Fintype.card_fin, hcard]
  intro r hr
  have hrmem : r ∈ rootSet :=
    Multiset.mem_toFinset.mpr (Polynomial.mem_roots'.mpr ⟨hP, hr⟩)
  rw [← himage, Finset.mem_image] at hrmem
  obtain ⟨i, -, hir⟩ := hrmem
  have hri : Literal.InInterval out.isolations[i].interval r := hir ▸ (hroot i).2
  refine ⟨i, hri, ?_⟩
  intro j hrj
  have hrj' : r = theRoot j := huniq j r ⟨hr, hrj⟩
  apply hinj
  rw [← hrj', hir]

end

end HexRealRootsMathlib
