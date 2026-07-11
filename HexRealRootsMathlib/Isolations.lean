/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib
public import HexRealRootsMathlib.ChainCorrespond
public import HexRealRoots.Var
-- `import all` on the executable modules so the non-`@[expose]` bodies of
-- `sturmChain`, `sturmCount`, `sturmVarAt`, and `signVar` unfold here (the
-- degree-positivity derivation reads the empty chain of a degree-`≤ 0` input).
import all HexRealRootsMathlib.Separation
import all HexRealRoots.Basic
import all HexRealRoots.Chain
import all HexRealRoots.Var

public section

/-!
# Isolation semantics

Soundness of a `RealRootIsolation`/`RealRootIsolations` witness, for any
rationally squarefree `p`, no matter which engine produced it:

* `RealRootIsolation.exists_unique_root`: a single certified isolation names
  exactly one real root in its half-open interval.
* `RealRootIsolations.isolates`: a complete run names every real root exactly
  once.

Both consume only the decidable certificate fields (`count_one`, `ordered`,
`complete`) plus the correspondence theorems `sturmCount_eq_card_roots` and
`rootCount_eq_card_roots` from `ChainCorrespond`.

The correspondence theorems carry a `1 ≤ (p.degree?).getD 0` hypothesis
(`SquareFreeRat` alone is insufficient — `SquareFreeRat 0` is vacuous). The
isolation theorems do **not** need it as a separate hypothesis: a
`RealRootIsolation` carries `count_one`, and a Sturm count of `1` forces a
nonempty chain, hence positive degree (`degree_pos_of_count_one`). So the
statements match the SPEC verbatim, taking only `SquareFreeRat p`.
-/

namespace HexRealRootsMathlib

open Polynomial

noncomputable section

variable {p : Hex.ZPoly}

/-- A polynomial of degree `≤ 0` has the empty Sturm chain. -/
private theorem sturmChain_eq_nil_of_degree_nonpos (h : (p.degree?).getD 0 = 0) :
    Hex.ZPoly.sturmChain p = #[] := by
  have hcase : p.degree? = none ∨ p.degree? = some 0 := by
    rcases hd : p.degree? with _ | n
    · exact Or.inl rfl
    · rcases n with _ | m
      · exact Or.inr rfl
      · rw [hd] at h; simp at h
  rcases hcase with hc | hc <;> simp only [Hex.ZPoly.sturmChain, hc]

/-- A Sturm count of `1` forces positive degree: a degree-`≤ 0` input has the
empty chain, whose count is `0` at every pair of endpoints. -/
theorem degree_pos_of_count_one (iso : Hex.RealRootIsolation p) :
    1 ≤ (p.degree?).getD 0 := by
  by_contra h
  have hz : (p.degree?).getD 0 = 0 := by omega
  have hc := iso.count_one
  unfold Hex.sturmCount at hc
  rw [sturmChain_eq_nil_of_degree_nonpos hz] at hc
  simp only [Hex.sturmVarAt, List.map_nil, Hex.signVar, List.filter_nil,
    Hex.signVar.go, Nat.cast_zero, sub_zero] at hc
  exact absurd hc (by norm_num)

/-- Dyadic order transfers to the real values. -/
private theorem toReal_le_toReal {a b : Dyadic} (h : a ≤ b) :
    Dyadic.toReal a ≤ Dyadic.toReal b := by
  have h2 : a.toRat ≤ b.toRat := Dyadic.toRat_le_toRat_iff.mpr h
  unfold Dyadic.toReal
  exact_mod_cast h2

/-- **Isolation soundness.** A certified isolation of `p` names exactly one real
root of `toPolyℝ p` in its half-open interval `(lower, upper]`. -/
theorem RealRootIsolation.exists_unique_root (hp : Hex.ZPoly.SquareFreeRat p)
    (iso : Hex.RealRootIsolation p) :
    ∃! r : ℝ, (toPolyℝ p).IsRoot r ∧
      Dyadic.toReal iso.interval.lower < r ∧ r ≤ Dyadic.toReal iso.interval.upper := by
  have hdeg : 1 ≤ (p.degree?).getD 0 := degree_pos_of_count_one iso
  have hp0 : p ≠ 0 := by
    intro hh; rw [hh] at hdeg; simp only [Hex.DensePoly.degree?_zero_getD] at hdeg; omega
  have hP0 : toPolyℝ p ≠ 0 := fun h => hp0 (toPolyℝ_eq_zero_iff.mp h)
  -- The filtered root multiset has card `1`.
  have hc := iso.count_one
  rw [sturmCount_eq_card_roots p hdeg hp iso.interval] at hc
  set M := (toPolyℝ p).roots.filter
    (fun r => Dyadic.toReal iso.interval.lower < r ∧ r ≤ Dyadic.toReal iso.interval.upper)
    with hMdef
  have hM : Multiset.card M = 1 := by exact_mod_cast hc
  obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp hM
  have hamem : a ∈ M := by rw [ha]; exact Multiset.mem_singleton_self a
  rw [hMdef, Multiset.mem_filter] at hamem
  obtain ⟨haroots, halo, hahi⟩ := hamem
  have haroot : (toPolyℝ p).IsRoot a := (Polynomial.mem_roots'.mp haroots).2
  refine ⟨a, ⟨haroot, halo, hahi⟩, ?_⟩
  rintro y ⟨hyroot, hylo, hyhi⟩
  have hyM : y ∈ M := by
    rw [hMdef, Multiset.mem_filter]
    exact ⟨Polynomial.mem_roots'.mpr ⟨hP0, hyroot⟩, hylo, hyhi⟩
  rw [ha, Multiset.mem_singleton] at hyM
  exact hyM

/-- **Completeness of a run.** A complete isolation run of a positive-degree,
rationally squarefree `p` names every real root of `toPolyℝ p` exactly once:
each root lies in exactly one of the emitted half-open intervals.

The SPEC states this with only `SquareFreeRat p`, but that is unsound: for
`p = 0` (which passes `SquareFreeRat`) every real is a root while `complete`
forces zero isolations, so no root is captured. The positive-degree hypothesis
`1 ≤ (p.degree?).getD 0` (equivalently `p ≠ 0` after excluding the vacuous
nonzero-constant case) is the honest hypothesis; it matches the correspondence
theorems `sturmCount_eq_card_roots`/`rootCount_eq_card_roots`. -/
theorem RealRootIsolations.isolates (hdeg : 1 ≤ (p.degree?).getD 0)
    (hp : Hex.ZPoly.SquareFreeRat p) (out : Hex.RealRootIsolations p) :
    ∀ r : ℝ, (toPolyℝ p).IsRoot r →
      ∃! iso ∈ out.isolations.toList,
        Dyadic.toReal iso.interval.lower < r ∧ r ≤ Dyadic.toReal iso.interval.upper := by
  have hp0 : p ≠ 0 := by
    intro hh; rw [hh] at hdeg; simp only [Hex.DensePoly.degree?_zero_getD] at hdeg; omega
  have hP0 : toPolyℝ p ≠ 0 := fun h => hp0 (toPolyℝ_eq_zero_iff.mp h)
  have hsep : (toPolyℝ p).Separable := separable_toPolyℝ p ((squareFreeRat_iff p hp0).mp hp)
  have hnodup : (toPolyℝ p).roots.Nodup := nodup_roots hsep
  -- The unique root of each isolation.
  have H : ∀ i : Fin out.isolations.size, ∃ y : ℝ,
      ((toPolyℝ p).IsRoot y ∧ Dyadic.toReal out.isolations[i].interval.lower < y ∧
          y ≤ Dyadic.toReal out.isolations[i].interval.upper) ∧
        ∀ z, ((toPolyℝ p).IsRoot z ∧ Dyadic.toReal out.isolations[i].interval.lower < z ∧
          z ≤ Dyadic.toReal out.isolations[i].interval.upper) → z = y :=
    fun i => RealRootIsolation.exists_unique_root hp out.isolations[i]
  choose theRoot hroot huniq using H
  -- `theRoot` is strictly increasing along the ordered isolations, hence injective.
  have hmono : ∀ i j : Fin out.isolations.size, (i : ℕ) < (j : ℕ) →
      theRoot i < theRoot j := by
    intro i j hij
    have hord := out.ordered i j hij
    calc theRoot i ≤ Dyadic.toReal out.isolations[i].interval.upper := (hroot i).2.2
      _ ≤ Dyadic.toReal out.isolations[j].interval.lower := toReal_le_toReal hord
      _ < theRoot j := (hroot j).2.1
  have hinj : Function.Injective theRoot := by
    intro i j hij
    rcases lt_trichotomy (i : ℕ) (j : ℕ) with h | h | h
    · exact absurd hij (ne_of_lt (hmono i j h))
    · exact Fin.ext h
    · exact absurd hij.symm (ne_of_lt (hmono j i h))
  -- The isolations' roots exhaust the root finset.
  set S := (toPolyℝ p).roots.toFinset with hSdef
  have hmemS : ∀ i, theRoot i ∈ S := fun i =>
    Multiset.mem_toFinset.mpr (Polynomial.mem_roots'.mpr ⟨hP0, (hroot i).1⟩)
  have hScard : S.card = out.isolations.size := by
    rw [hSdef, Multiset.toFinset_card_of_nodup hnodup,
      ← rootCount_eq_card_roots p hdeg hp, ← out.complete]
  have himage : Finset.image theRoot Finset.univ = S := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact hmemS i
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin, hScard]
  -- The main statement.
  intro r hr
  have hrS : r ∈ S := Multiset.mem_toFinset.mpr (Polynomial.mem_roots'.mpr ⟨hP0, hr⟩)
  rw [← himage, Finset.mem_image] at hrS
  obtain ⟨i, -, hi_eq⟩ := hrS
  -- Existence: the `i`-th isolation contains `r`.
  have hmem_i : out.isolations[i] ∈ out.isolations.toList := Array.getElem_mem_toList _
  have hlo_i : Dyadic.toReal out.isolations[i].interval.lower < r := hi_eq ▸ (hroot i).2.1
  have hhi_i : r ≤ Dyadic.toReal out.isolations[i].interval.upper := hi_eq ▸ (hroot i).2.2
  refine ⟨out.isolations[i], ⟨hmem_i, hlo_i, hhi_i⟩, ?_⟩
  -- Uniqueness.
  rintro iso' ⟨hiso'mem, hiso'lo, hiso'hi⟩
  rw [Array.mem_toList_iff, Array.mem_iff_getElem] at hiso'mem
  obtain ⟨j, hj, hjeq⟩ := hiso'mem
  have hjeq' : out.isolations[(⟨j, hj⟩ : Fin out.isolations.size)] = iso' := hjeq
  -- `r` is the unique root of the `j`-th isolation, so `theRoot j = r`.
  have hrj : r = theRoot ⟨j, hj⟩ := by
    refine huniq ⟨j, hj⟩ r ⟨hr, ?_, ?_⟩
    · rw [hjeq']; exact hiso'lo
    · rw [hjeq']; exact hiso'hi
  have hij : (⟨j, hj⟩ : Fin out.isolations.size) = i := by
    apply hinj; rw [← hrj, hi_eq]
  exact hjeq'.symm.trans
    (congrArg (fun k : Fin out.isolations.size => out.isolations[k]) hij)

end

end HexRealRootsMathlib
