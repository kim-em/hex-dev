/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexNumberFieldMathlib.Nearest
public import HexNumberFieldMathlib.ComponentRoots
public import Mathlib.Data.Prod.Lex
public section

/-! Root enumeration is a total preorder on canonical centre keys. -/
namespace Hex.AlgebraicNumber

private def sideRank (a : AlgebraicNumber) : Nat := if a.side = .lower then 0 else 1

/-- The deterministic enumeration key, distinct from the complex partial order. -/
noncomputable def rootKey (a : AlgebraicNumber) :
    Nat ×ₗ (Rat ×ₗ (Rat ×ₗ (Int ×ₗ (List Int ×ₗ Nat)))) :=
  let s := a.isolation.base.1.square
  if a.isReal then toLex (0, toLex (s.re.toRat, toLex (s.im.toRat, toLex (s.prec, toLex ([], 0)))))
  else toLex (1, toLex (s.im.toRat, toLex (s.re.toRat,
    toLex (s.prec, toLex (a.p.toArray.toList, sideRank a)))))

private theorem polynomial_eq (p q : ZPoly) : p.toArray.toList = q.toArray.toList ↔ p = q := by
  constructor
  · intro h
    have harr := Array.toList_inj.mp h
    apply DensePoly.ext_coeff
    intro n
    rw [← DensePoly.toArray_getD, harr, DensePoly.toArray_getD]
  · rintro rfl
    rfl

private theorem polynomial_array_eq (p q : ZPoly) : p.toArray = q.toArray ↔ p = q := by
  rw [← polynomial_eq, Array.toList_inj]

private theorem rank_le_iff (a b : AlgebraicNumber) :
    sideRank a ≤ sideRank b ↔ a.side = .lower ∨ b.side ≠ .lower := by
  by_cases ha : a.side = .lower <;> by_cases hb : b.side = .lower <;> simp [sideRank, ha, hb]

/-- The executable enumeration comparator is lexicographic comparison of its key. -/
theorem rootLe_iff (a b : AlgebraicNumber) : rootLe a b = true ↔ rootKey a ≤ rootKey b := by
  cases ha : a.isReal <;> cases hb : b.isReal
  · simp only [rootLe, ha, hb]
    split_ifs <;>
      simp_all [rootKey, Prod.Lex.toLex_le_toLex, Dyadic.toRat_inj,
        Dyadic.toRat_lt_toRat_iff, PolyQuot.Roots.intListLe_iff, polynomial_array_eq, rank_le_iff]
    all_goals simp_all [le_iff_lt_or_eq, polynomial_array_eq]
  · simp [rootLe, rootKey, ha, hb, Prod.Lex.toLex_le_toLex]
  · simp [rootLe, rootKey, ha, hb, Prod.Lex.toLex_le_toLex]
  · simp only [rootLe, ha, hb]
    split_ifs <;>
      simp_all [rootKey, Prod.Lex.toLex_le_toLex, Dyadic.toRat_inj,
        Dyadic.toRat_lt_toRat_iff]
    all_goals simp_all [le_iff_lt_or_eq]

/-- Enumeration comparison is transitive. -/
theorem rootLe_trans (a b c : AlgebraicNumber) (hab : rootLe a b = true)
    (hbc : rootLe b c = true) : rootLe a c = true :=
  (rootLe_iff a c).mpr (((rootLe_iff a b).mp hab).trans ((rootLe_iff b c).mp hbc))

/-- Any two canonical numbers are comparable for enumeration. -/
theorem rootLe_total (a b : AlgebraicNumber) : (rootLe a b || rootLe b a) = true := by
  rcases le_total (rootKey a) (rootKey b) with h | h
  · simp [(rootLe_iff a b).mpr h]
  · simp [(rootLe_iff b a).mpr h]

private theorem roots_eq {p q : ZPoly} (r : RefinedIsolation p) (s : RefinedIsolation q)
    (hp : p = q) (hs : r.1.square = s.1.square) : r.root = s.root := by
  cases hp
  apply (HexRootsMathlib.RefinedIsolation.intersects_iff_root_eq r s).mp
  change r.1.square.discsMeet s.1.square = true
  rw [hs]
  exact HexRootsMathlib.RefinedIsolation.intersects_equivalence.refl s

private theorem oriented_eq {p q : ZPoly} (r : OrientedIsolation p) (s : OrientedIsolation q)
    (hp : p = q) (hs : r.base.1.square = s.base.1.square) (hside : r.side = s.side) :
    r.rep.root = s.rep.root := by
  have hr := roots_eq r.base s.base hp hs
  unfold OrientedIsolation.rep
  rw [hside]
  cases h : s.side <;> simp [hr, HexRootsMathlib.RefinedIsolation.root_conj]

/-- Nonreal enumeration keys determine the canonical value. -/
theorem eq_of_rootKey {a b : AlgebraicNumber} (ha : a.isReal = false) (hb : b.isReal = false)
    (h : rootKey a = rootKey b) : a = b := by
  have hc : a.isolation.base.1.square.im.toRat = b.isolation.base.1.square.im.toRat ∧
      a.isolation.base.1.square.re.toRat = b.isolation.base.1.square.re.toRat ∧
      a.isolation.base.1.square.prec = b.isolation.base.1.square.prec ∧
      a.p.toArray.toList = b.p.toArray.toList ∧ sideRank a = sideRank b := by
    simpa [rootKey, ha, hb] using h
  have hs : a.side = b.side := by
    have hr := hc.2.2.2.2
    cases hsa : a.side <;> cases hsb : b.side <;> simp_all [isReal, sideRank]
  have hp := (polynomial_eq a.p b.p).mp hc.2.2.2.1
  have hsq : a.isolation.base.1.square = b.isolation.base.1.square := by
    have hre := Dyadic.toRat_inj.mp hc.2.1
    have him := Dyadic.toRat_inj.mp hc.1
    have hprec := hc.2.2.1
    have hext : ∀ s t : DyadicSquare,
        s.re = t.re → s.im = t.im → s.prec = t.prec → s = t := by
      intro ⟨_, _, _⟩ ⟨_, _, _⟩
      simp_all
    exact hext _ _ hre him hprec
  apply toComplex_injective
  exact oriented_eq a.isolation b.isolation hp hsq hs

private theorem lex_between {α β : Type*} [LinearOrder α] [LinearOrder β]
    {x y : α} {a b c : β} (h₁ : toLex (x, a) ≤ toLex (y, c))
    (h₂ : toLex (y, c) ≤ toLex (x, b)) : x = y ∧ a ≤ c ∧ c ≤ b := by
  rw [Prod.Lex.toLex_le_toLex] at h₁ h₂
  have hxy : x ≤ y := h₁.elim le_of_lt (fun h => h.1.le)
  have hyx : y ≤ x := h₂.elim le_of_lt (fun h => h.1.le)
  have he := hxy.antisymm hyx
  subst y
  simpa using And.intro h₁ h₂

/-- The lower member precedes its upper conjugate. -/
theorem rootLe_conj (a : AlgebraicNumber) (ha : a.side = .lower) : rootLe a a.conj = true := by
  rw [rootLe_iff]
  simp [rootKey, isReal, ha, conj_side, conj_base_square, conj_p, sideRank,
    Prod.Lex.toLex_le_toLex]

/-- A nonreal lower root and its conjugate have no other canonical value between them. -/
theorem between_conjugates (a b : AlgebraicNumber) (ha : a.side = .lower)
    (hab : rootLe a b = true) (hba : rootLe b a.conj = true) : b = a ∨ b = a.conj := by
  have har : a.isReal = false := by simp [isReal, ha]
  have hac : a.conj.isReal = false := by simp [isReal, conj_side, ha]
  have h₁ := (rootLe_iff a b).mp hab
  have h₂ := (rootLe_iff b a.conj).mp hba
  have hb : b.isReal = false := by
    cases hr : b.isReal
    · rfl
    · simp [rootKey, har, hr, Prod.Lex.toLex_le_toLex] at h₁
  simp only [rootKey, har, hb, hac, Bool.false_eq_true, ↓reduceIte,
    conj_base_square, conj_p, sideRank, conj_side, ha, ↓reduceIte] at h₁ h₂
  obtain ⟨_, h₁, h₂⟩ := lex_between h₁ h₂
  obtain ⟨him, h₁, h₂⟩ := lex_between h₁ h₂
  obtain ⟨hre, h₁, h₂⟩ := lex_between h₁ h₂
  obtain ⟨hprec, h₁, h₂⟩ := lex_between h₁ h₂
  obtain ⟨hp, _, _⟩ := lex_between h₁ h₂
  by_cases hs : b.side = .lower
  · left
    apply eq_of_rootKey hb har
    simp [rootKey, har, hb, sideRank, hs, ha, him, hre, hprec, hp]
  · right
    apply eq_of_rootKey hb hac
    simp [rootKey, hb, hac, sideRank, conj_side, conj_base_square, conj_p,
      hs, ha, him, hre, hprec, hp]

end Hex.AlgebraicNumber

namespace Hex.ZPoly

/-- Integer root enumeration is sorted by its canonical centre key. -/
theorem algebraicRoots_sorted (p : ZPoly) :
    (ZPoly.algebraicRoots p).toList.Pairwise (fun a b => AlgebraicNumber.rootLe a b = true) := by
  have h := algebraicRoots?_eq p
  unfold ZPoly.algebraicRoots? at h
  split at h
  · have he := (Option.some.inj h).symm
    simp [he]
  · dsimp only at h
    split at h
    · split at h
      · split at h
        · split at h
          · obtain ⟨isolations, _, h⟩ := Option.bind_eq_some_iff.mp h
            obtain ⟨refined, _, h⟩ := Option.bind_eq_some_iff.mp h
            obtain ⟨roots, _, h⟩ := Option.bind_eq_some_iff.mp h
            have he := (Option.some.inj h).symm
            rw [he, List.toList_toArray]
            exact List.pairwise_mergeSort AlgebraicNumber.rootLe_trans AlgebraicNumber.rootLe_total _
          · simp at h
        · simp at h
      · simp at h
    · simp at h

/-- The conjugate of every listed root is listed too. -/
theorem conj_mem_algebraicRoots {p : ZPoly} (hp : p ≠ 0) {a : AlgebraicNumber}
    (ha : a ∈ ZPoly.algebraicRoots p) : a.conj ∈ ZPoly.algebraicRoots p := by
  have hr := (mem_algebraicRoots_iff p hp a.toComplex).mp
    ⟨a, Array.mem_toList_iff.mpr ha, rfl⟩
  have hc := HexRootsMathlib.ZPoly.isRoot_conj hr
  rw [← AlgebraicNumber.conj_toComplex] at hc
  obtain ⟨b, hb, he⟩ := (mem_algebraicRoots_iff p hp a.conj.toComplex).mpr hc
  have heq := AlgebraicNumber.toComplex_injective he
  subst b
  exact Array.mem_toList_iff.mp hb

end Hex.ZPoly

/-- info: 'Hex.AlgebraicNumber.between_conjugates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.AlgebraicNumber.between_conjugates
