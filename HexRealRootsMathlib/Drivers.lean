/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib
public import HexRealRootsMathlib.ChainCorrespond
public import HexRealRootsMathlib.Isolations
public import HexRealRoots.Isolate
public import HexRealRoots.Refine
-- `import all` on the executable modules so the non-`@[expose]` bodies of the
-- isolation engines (`sturmChain`, `sturmVarAt`, `sturmVisit`, `refine1`,
-- `isolateSturm?`, `isolate?`, and the dyadic evaluation helpers) unfold here.
import all HexRealRootsMathlib.Separation
import all HexRealRoots.Basic
import all HexRealRoots.Chain
import all HexRealRoots.Var
import all HexRealRoots.Prec
import all HexRealRoots.Refine
import all HexRealRoots.IsolateSturm
import all HexRealRoots.Isolate

public section

/-!
# Driver completeness and refinement

* `refine1_isolates_same`: one bisection refinement preserves the isolated root
  and halves the interval width (the fallback branch is unreachable for
  squarefree `p`).
* `isolateSturm?_isSome`, `isolate?_isSome`: the Sturm engine (and hence the
  top-level driver) succeeds on nonzero squarefree input (positive degree is
  the real content; a nonzero constant certifies through the empty chain).

## The `±rootBound` counts match `rootCount` with no chain-element gap

The engine seeds `sturmVisit` with the memoised counts `sturmVarAt chain (−R)`
and `sturmVarAt chain (+R)` at `R = rootBound p`, and `assemble?` later checks
the emitted total against `sturmVarNegInf chain − sturmVarPosInf chain =
rootCount p`. One might worry that a *chain element* (a remainder of `(p, p')`,
not `p` itself) could have a real root beyond `rootBound p`, so that the
endpoint variation counts at `±R` disagree with the `±∞` counts.

There is no such gap. `sturmCount_eq_card_roots` proves
`sturmVarAt chain (−R) − sturmVarAt chain (+R)` equals the number of roots of
**`p`** in `(−R, R]` — a statement about `p`'s roots only, with the chain
elements' own zeros already fully accounted for by Sturm's theorem. Since
`rootBound_bounds_roots` places every real root of `p` inside `(−R, R]`, that
count is `rootCount p` (via `rootCount_eq_card_roots`), regardless of where the
chain elements vanish. So the telescoping total the engine checks always
matches, and the check never spuriously fails.
-/

namespace HexRealRootsMathlib

open Polynomial

noncomputable section

variable {p : Hex.ZPoly}

/-! ### Dyadic midpoint arithmetic -/

/-- Dyadic order coincides with the order of the real values. -/
private theorem toReal_lt_toReal_iff {a b : Dyadic} :
    Dyadic.toReal a < Dyadic.toReal b ↔ a < b := by
  unfold Dyadic.toReal
  rw [Rat.cast_lt, Dyadic.toRat_lt_toRat_iff]

/-- Transitivity of the core dyadic `<` (routed through `toRat`, to stay in the
`Dyadic.instLT` instance that `DyadicInterval.lt` uses). -/
private theorem dlt_trans {a b c : Dyadic} (h1 : a < b) (h2 : b < c) : a < c := by
  rw [← Dyadic.toRat_lt_toRat_iff] at h1 h2 ⊢
  exact lt_trans h1 h2

/-- Dyadic `≤` transfers to the real values. -/
private theorem toReal_le_toReal {a b : Dyadic} (h : a ≤ b) :
    Dyadic.toReal a ≤ Dyadic.toReal b := by
  have h2 : a.toRat ≤ b.toRat := Dyadic.toRat_le_toRat_iff.mpr h
  unfold Dyadic.toReal; exact_mod_cast h2

/-- A right shift by one bit halves the real value. -/
private theorem toReal_shiftRight_one (x : Dyadic) :
    Dyadic.toReal (x >>> (1 : Int)) = Dyadic.toReal x / 2 := by
  have h : x >>> (1 : Int) = x <<< (-1 : Int) := by cases x <;> rfl
  unfold Dyadic.toReal
  rw [h, toRat_shiftLeft]
  push_cast
  ring

/-- `Dyadic.toReal` is subtractive. -/
private theorem toReal_sub (a b : Dyadic) :
    Dyadic.toReal (a - b) = Dyadic.toReal a - Dyadic.toReal b := by
  unfold Dyadic.toReal; rw [Dyadic.toRat_sub]; push_cast; ring

/-- The real value of an interval's dyadic midpoint. -/
private theorem toReal_midpoint (I : Hex.DyadicInterval) :
    Dyadic.toReal I.midpoint = (Dyadic.toReal I.lower + Dyadic.toReal I.upper) / 2 := by
  unfold Hex.DyadicInterval.midpoint
  rw [toReal_shiftRight_one, toReal_add]

/-- The midpoint is strictly above the lower endpoint. -/
private theorem lower_lt_midpoint (I : Hex.DyadicInterval) : I.lower < I.midpoint := by
  rw [← toReal_lt_toReal_iff, toReal_midpoint]
  have := toReal_lt_toReal_iff.mpr I.lt
  linarith

/-- The midpoint is strictly below the upper endpoint. -/
private theorem midpoint_lt_upper (I : Hex.DyadicInterval) : I.midpoint < I.upper := by
  rw [← toReal_lt_toReal_iff, toReal_midpoint]
  have := toReal_lt_toReal_iff.mpr I.lt
  linarith

/-! ### Additivity of the Sturm count across a midpoint -/

/-- **Sturm count is additive across a splitting point.** For a positive-degree
squarefree `p` and `lo < mid < hi`, the count over `(lo, hi]` is the sum of the
counts over `(lo, mid]` and `(mid, hi]`: the half-open interval splits as a
disjoint union, and the root-filter cardinalities add. -/
private theorem sturmCount_split (hdeg : 1 ≤ (p.degree?).getD 0)
    (hp : Hex.ZPoly.SquareFreeRat p) {lo mid hi : Dyadic} (h1 : lo < mid) (h2 : mid < hi) :
    Hex.sturmCount p ⟨lo, hi, dlt_trans h1 h2⟩
      = Hex.sturmCount p ⟨lo, mid, h1⟩ + Hex.sturmCount p ⟨mid, hi, h2⟩ := by
  rw [sturmCount_eq_card_roots p hdeg hp, sturmCount_eq_card_roots p hdeg hp,
    sturmCount_eq_card_roots p hdeg hp]
  dsimp only
  have hlm : Dyadic.toReal lo < Dyadic.toReal mid := toReal_lt_toReal_iff.mpr h1
  have hmh : Dyadic.toReal mid < Dyadic.toReal hi := toReal_lt_toReal_iff.mpr h2
  set S := (toPolyℝ p).roots with hSdef
  classical
  have hadd := Multiset.filter_add_filter
    (fun r : ℝ => Dyadic.toReal mid < r ∧ r ≤ Dyadic.toReal hi) S
    (p := fun r : ℝ => Dyadic.toReal lo < r ∧ r ≤ Dyadic.toReal mid)
  have e1 : S.filter (fun r => (Dyadic.toReal lo < r ∧ r ≤ Dyadic.toReal mid) ∨
        (Dyadic.toReal mid < r ∧ r ≤ Dyadic.toReal hi))
      = S.filter (fun r => Dyadic.toReal lo < r ∧ r ≤ Dyadic.toReal hi) := by
    refine Multiset.filter_congr (fun r _ => ?_)
    constructor
    · rintro (⟨a, b⟩ | ⟨a, b⟩)
      · exact ⟨a, le_trans b (le_of_lt hmh)⟩
      · exact ⟨lt_trans hlm a, b⟩
    · rintro ⟨a, b⟩
      rcases le_or_gt r (Dyadic.toReal mid) with hle | hlt
      · exact Or.inl ⟨a, hle⟩
      · exact Or.inr ⟨hlt, b⟩
  have e2 : S.filter (fun r => (Dyadic.toReal lo < r ∧ r ≤ Dyadic.toReal mid) ∧
        (Dyadic.toReal mid < r ∧ r ≤ Dyadic.toReal hi)) = 0 := by
    rw [Multiset.filter_eq_nil]
    rintro r _ ⟨⟨_, b⟩, c, _⟩
    exact absurd (lt_of_le_of_lt b c) (lt_irrefl _)
  rw [e1, e2, add_zero] at hadd
  have hnat : (S.filter (fun r => Dyadic.toReal lo < r ∧ r ≤ Dyadic.toReal hi)).card
      = (S.filter (fun r => Dyadic.toReal lo < r ∧ r ≤ Dyadic.toReal mid)).card
        + (S.filter (fun r => Dyadic.toReal mid < r ∧ r ≤ Dyadic.toReal hi)).card := by
    rw [← hadd, Multiset.card_add, Nat.add_comm]
  exact_mod_cast hnat

/-- A count-`0` interval contains no real root of `p`. -/
private theorem no_root_of_count_zero (hdeg : 1 ≤ (p.degree?).getD 0)
    (hp : Hex.ZPoly.SquareFreeRat p) {J : Hex.DyadicInterval} (h : Hex.sturmCount p J = 0)
    (hP0 : toPolyℝ p ≠ 0) {r : ℝ} (hr : (toPolyℝ p).IsRoot r)
    (hlo : Dyadic.toReal J.lower < r) (hhi : r ≤ Dyadic.toReal J.upper) : False := by
  rw [sturmCount_eq_card_roots p hdeg hp] at h
  have hcard : ((toPolyℝ p).roots.filter
      (fun r => Dyadic.toReal J.lower < r ∧ r ≤ Dyadic.toReal J.upper)).card = 0 := by
    exact_mod_cast h
  have hmem : r ∈ (toPolyℝ p).roots.filter
      (fun r => Dyadic.toReal J.lower < r ∧ r ≤ Dyadic.toReal J.upper) := by
    rw [Multiset.mem_filter]
    exact ⟨Polynomial.mem_roots'.mpr ⟨hP0, hr⟩, hlo, hhi⟩
  have hpos := Multiset.card_pos_iff_exists_mem.mpr ⟨r, hmem⟩
  omega

/-! ### Refinement preserves the isolated root -/

/-- **One refinement step preserves the root and halves the width.** For a
squarefree `p`, `iso.refine1` isolates the same real root as `iso` (a root lies
in `iso`'s interval iff it lies in the refined interval) and its width is exactly
half. The fallback branch of `refine1` is never taken: the two half-counts sum
to `1`, so exactly one half certifies. -/
theorem refine1_isolates_same (hp : Hex.ZPoly.SquareFreeRat p)
    (iso : Hex.RealRootIsolation p) :
    (∀ r : ℝ, (toPolyℝ p).IsRoot r →
        (Dyadic.toReal iso.interval.lower < r ∧ r ≤ Dyadic.toReal iso.interval.upper ↔
          Dyadic.toReal iso.refine1.interval.lower < r ∧
            r ≤ Dyadic.toReal iso.refine1.interval.upper))
      ∧ Dyadic.toReal iso.refine1.interval.width
          = Dyadic.toReal iso.interval.width / 2 := by
  have hdeg := degree_pos_of_count_one iso
  have hp0 : p ≠ 0 := by
    intro hh; rw [hh] at hdeg; simp only [Hex.DensePoly.degree?_zero_getD] at hdeg; omega
  have hP0 : toPolyℝ p ≠ 0 := fun h => hp0 (toPolyℝ_eq_zero_iff.mp h)
  set lo := iso.interval.lower with hlodef
  set hi := iso.interval.upper with hhidef
  set m := iso.interval.midpoint with hmdef
  have hlm : lo < m := lower_lt_midpoint iso.interval
  have hmh : m < hi := midpoint_lt_upper iso.interval
  have htlm : Dyadic.toReal lo < Dyadic.toReal m := toReal_lt_toReal_iff.mpr hlm
  have htmh : Dyadic.toReal m < Dyadic.toReal hi := toReal_lt_toReal_iff.mpr hmh
  -- The two half-counts sum to 1.
  have hcount1 : Hex.sturmCount p ⟨lo, m, hlm⟩ + Hex.sturmCount p ⟨m, hi, hmh⟩ = 1 := by
    rw [← sturmCount_split hdeg hp hlm hmh]; exact iso.count_one
  have hCL0 : 0 ≤ Hex.sturmCount p ⟨lo, m, hlm⟩ := by
    rw [sturmCount_eq_card_roots p hdeg hp]; exact Int.natCast_nonneg _
  have hCR0 : 0 ≤ Hex.sturmCount p ⟨m, hi, hmh⟩ := by
    rw [sturmCount_eq_card_roots p hdeg hp]; exact Int.natCast_nonneg _
  -- The refined width is half, independent of the branch.
  have hwidth_left : Dyadic.toReal (Hex.DyadicInterval.width ⟨lo, m, hlm⟩)
      = Dyadic.toReal iso.interval.width / 2 := by
    show Dyadic.toReal (m - lo) = Dyadic.toReal (iso.interval.width) / 2
    rw [toReal_sub]
    show _ = Dyadic.toReal (hi - lo) / 2
    rw [toReal_sub, toReal_midpoint]; ring
  have hwidth_right : Dyadic.toReal (Hex.DyadicInterval.width ⟨m, hi, hmh⟩)
      = Dyadic.toReal iso.interval.width / 2 := by
    show Dyadic.toReal (hi - m) = Dyadic.toReal (iso.interval.width) / 2
    rw [toReal_sub]
    show _ = Dyadic.toReal (hi - lo) / 2
    rw [toReal_sub, toReal_midpoint]; ring
  by_cases hCL : Hex.sturmCount p ⟨lo, m, hlm⟩ = 1
  · -- Left half certifies: refined interval is `(lo, m]`.
    have hCLraw : ((Hex.sturmVarAt (Hex.ZPoly.sturmChain p) iso.interval.lower : Int)
        - Hex.sturmVarAt (Hex.ZPoly.sturmChain p) iso.interval.midpoint) = 1 := hCL
    have href : iso.refine1.interval = (⟨lo, m, hlm⟩ : Hex.DyadicInterval) := by
      show (Hex.RealRootIsolation.refine1 iso).interval = _
      unfold Hex.RealRootIsolation.refine1
      rw [dif_pos hlm, dif_pos hCLraw]
      rfl
    have hCR : Hex.sturmCount p ⟨m, hi, hmh⟩ = 0 := by omega
    refine ⟨fun r hr => ?_, ?_⟩
    · rw [href]
      constructor
      · rintro ⟨hrlo, hrhi⟩
        refine ⟨hrlo, ?_⟩
        by_contra hgt
        exact no_root_of_count_zero hdeg hp hCR hP0 hr (not_le.mp hgt) hrhi
      · rintro ⟨hrlo, hrhi⟩
        exact ⟨hrlo, le_trans hrhi (le_of_lt htmh)⟩
    · rw [href]; exact hwidth_left
  · -- Right half certifies: refined interval is `(m, hi]`.
    have hCR : Hex.sturmCount p ⟨m, hi, hmh⟩ = 1 := by omega
    have hCLz : Hex.sturmCount p ⟨lo, m, hlm⟩ = 0 := by omega
    have hCLraw_neg : ¬((Hex.sturmVarAt (Hex.ZPoly.sturmChain p) iso.interval.lower : Int)
        - Hex.sturmVarAt (Hex.ZPoly.sturmChain p) iso.interval.midpoint) = 1 := hCL
    have hCRraw : ((Hex.sturmVarAt (Hex.ZPoly.sturmChain p) iso.interval.midpoint : Int)
        - Hex.sturmVarAt (Hex.ZPoly.sturmChain p) iso.interval.upper) = 1 := hCR
    have href : iso.refine1.interval = (⟨m, hi, hmh⟩ : Hex.DyadicInterval) := by
      show (Hex.RealRootIsolation.refine1 iso).interval = _
      unfold Hex.RealRootIsolation.refine1
      rw [dif_pos hlm, dif_neg hCLraw_neg, dif_pos hmh, dif_pos hCRraw]
      rfl
    refine ⟨fun r hr => ?_, ?_⟩
    · rw [href]
      constructor
      · rintro ⟨hrlo, hrhi⟩
        refine ⟨?_, hrhi⟩
        by_contra hle
        exact no_root_of_count_zero hdeg hp hCLz hP0 hr hrlo (not_lt.mp hle)
      · rintro ⟨hrlo, hrhi⟩
        exact ⟨lt_trans htlm hrlo, hrhi⟩
    · rw [href]; exact hwidth_right

/-! ### The initial interval carries all roots: `±rootBound` counts `rootCount` -/

/-- `Dyadic.toReal` is negation-compatible. -/
private theorem toReal_neg (x : Dyadic) : Dyadic.toReal (-x) = -Dyadic.toReal x := by
  unfold Dyadic.toReal; rw [Dyadic.toRat_neg]; push_cast; ring

/-- The power-of-two root bound has positive real value. -/
private theorem rootBound_pos (p : Hex.ZPoly) : 0 < Dyadic.toReal (Hex.rootBound p) := by
  rcases hd : p.degree? with _ | d
  · rw [Hex.rootBound_of_degree?_none hd, toReal_ofInt]; norm_num
  · rcases d with _ | d'
    · rw [Hex.rootBound_of_degree?_zero hd, toReal_ofInt]; norm_num
    · rw [Hex.rootBound_of_degree?_pos hd, toReal_twoPow]; positivity

/-- `-rootBound p < rootBound p`, so the initial interval is nonempty. -/
private theorem neg_rootBound_lt_rootBound (p : Hex.ZPoly) :
    -(Hex.rootBound p) < Hex.rootBound p := by
  rw [← toReal_lt_toReal_iff, toReal_neg]
  have := rootBound_pos p; linarith

/-- **The `±rootBound` variation gap equals `rootCount`.** The Sturm variation
difference between `-rootBound p` and `rootBound p` counts the real roots of `p`
in `(-R, R]`, which is *every* real root (Cauchy bound), i.e. `rootCount p`. This
is a statement about `p`'s roots only — the chain elements' own (possibly larger)
zeros never enter, so there is no `±R`-versus-`±∞` gap. -/
private theorem sturmVar_neg_pos_sub (hdeg : 1 ≤ (p.degree?).getD 0)
    (hp : Hex.ZPoly.SquareFreeRat p) :
    (Hex.sturmVarAt (Hex.ZPoly.sturmChain p) (-(Hex.rootBound p)) : ℤ)
      - Hex.sturmVarAt (Hex.ZPoly.sturmChain p) (Hex.rootBound p)
      = Hex.rootCount p := by
  have hp0 : p ≠ 0 := by
    intro hh; rw [hh] at hdeg; simp only [Hex.DensePoly.degree?_zero_getD] at hdeg; omega
  have hP0 : toPolyℝ p ≠ 0 := fun h => hp0 (toPolyℝ_eq_zero_iff.mp h)
  have hR : -(Hex.rootBound p) < Hex.rootBound p := neg_rootBound_lt_rootBound p
  have hcount := sturmCount_eq_card_roots p hdeg hp ⟨-(Hex.rootBound p), Hex.rootBound p, hR⟩
  have hfilter : ((toPolyℝ p).roots.filter
      (fun r => Dyadic.toReal (-(Hex.rootBound p)) < r ∧ r ≤ Dyadic.toReal (Hex.rootBound p)))
      = (toPolyℝ p).roots := by
    rw [Multiset.filter_eq_self]
    intro r hr
    have hroot : (toPolyℝ p).IsRoot r := (Polynomial.mem_roots'.mp hr).2
    have hb := rootBound_bounds_roots p hP0 r hroot
    rw [toReal_neg]
    obtain ⟨h1, h2⟩ := abs_lt.mp hb
    exact ⟨h1, le_of_lt h2⟩
  rw [hfilter] at hcount
  rw [rootCount_eq_card_roots p hdeg hp]
  exact hcount

/-- `ceilLog2Dyadic` is a genuine base-two ceiling on positive dyadics:
`toReal x ≤ 2 ^ (ceilLog2Dyadic x)`. -/
private theorem toReal_le_two_pow_ceilLog2Dyadic (x : Dyadic) (hx : 0 < Dyadic.toReal x) :
    Dyadic.toReal x ≤ (2 : ℝ) ^ (Hex.ceilLog2Dyadic x) := by
  cases x with
  | zero => simp [Dyadic.toReal] at hx
  | ofOdd n k hn =>
    have htr : Dyadic.toReal (Dyadic.ofOdd n k hn) = (n : ℝ) * 2 ^ (-k : Int) := by
      unfold Dyadic.toReal; rw [Dyadic.toRat_ofOdd_eq_mul_two_pow]; push_cast; ring
    have h2k : (0 : ℝ) < 2 ^ (-k : Int) := by positivity
    have hn0 : 0 < n := by
      by_contra h
      rw [htr] at hx
      have : (n : ℝ) ≤ 0 := by exact_mod_cast (not_lt.mp h)
      nlinarith [hx, h2k, this]
    have hcl : Hex.ceilLog2Dyadic (Dyadic.ofOdd n k hn)
        = (Hex.ceilLog2Nat n.toNat : Int) - k := by
      show (if n ≤ 0 then (0 : Int) else (Hex.ceilLog2Nat n.toNat : Int) - k) = _
      rw [if_neg (by omega)]
    have hnle : (n : ℝ) ≤ (2 : ℝ) ^ (Hex.ceilLog2Nat n.toNat) := by
      have hnat := le_two_pow_ceilLog2Nat n.toNat
      have hcast : (n.toNat : ℝ) ≤ (2 : ℝ) ^ (Hex.ceilLog2Nat n.toNat) := by exact_mod_cast hnat
      calc (n : ℝ) = (n.toNat : ℝ) := by exact_mod_cast (Int.toNat_of_nonneg (le_of_lt hn0)).symm
        _ ≤ _ := hcast
    rw [htr, hcl,
      show (Hex.ceilLog2Nat n.toNat : Int) - k = (Hex.ceilLog2Nat n.toNat : Int) + (-k) by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
    exact mul_le_mul_of_nonneg_right hnle (le_of_lt h2k)

/-- **The initial interval's width fits the depth budget.** For positive-degree
`p`, `2 · rootBound p ≤ 2 ^ (isolationDepth p − sepPrec p)`, which is the
depth-sufficiency hypothesis the `sturmVisit` induction consumes at the top. -/
private theorem initial_width_le (p : Hex.ZPoly) (hdeg : 1 ≤ (p.degree?).getD 0) :
    Dyadic.toReal (Hex.rootBound p) - Dyadic.toReal (-(Hex.rootBound p))
      ≤ (2 : ℝ) ^ ((Hex.isolationDepth p : ℤ) - (Hex.sepPrec p : ℤ)) := by
  obtain ⟨d, hd⟩ : ∃ d, p.degree? = some (d + 1) := by
    rcases hh : p.degree? with _ | n
    · rw [hh] at hdeg; simp at hdeg
    · rcases n with _ | m
      · rw [hh] at hdeg; simp at hdeg
      · exact ⟨m, rfl⟩
  have hlhs : Dyadic.toReal (Hex.rootBound p) - Dyadic.toReal (-(Hex.rootBound p))
      = Dyadic.toReal (Dyadic.ofInt 2 * Hex.rootBound p) := by
    rw [toReal_neg, toReal_mul, toReal_ofInt]; push_cast; ring
  have hpos : 0 < Dyadic.toReal (Dyadic.ofInt 2 * Hex.rootBound p) := by
    rw [← hlhs, toReal_neg]; have := rootBound_pos p; linarith
  have hdepth : (Hex.isolationDepth p : ℤ) - (Hex.sepPrec p : ℤ)
      = ((Hex.ceilLog2Dyadic (Dyadic.ofInt 2 * Hex.rootBound p)).toNat : ℤ)
        + (Hex.depthSlack : ℤ) := by
    simp only [Hex.isolationDepth, hd]
    push_cast; ring
  rw [hlhs, hdepth]
  refine le_trans (toReal_le_two_pow_ceilLog2Dyadic _ hpos) ?_
  refine zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ?_
  have hself := Int.self_le_toNat (Hex.ceilLog2Dyadic (Dyadic.ofInt 2 * Hex.rootBound p))
  have hslack : (0 : ℤ) ≤ (Hex.depthSlack : ℤ) := by positivity
  linarith

/-! ### The `sturmVisit` worklist drains -/

/-- Dyadic `≤` is reflexive (routed through `toRat`, staying in the core
instances that `DyadicInterval` uses). -/
private theorem dle_refl (a : Dyadic) : a ≤ a :=
  Dyadic.toRat_le_toRat_iff.mp (le_refl _)

/-- Dyadic `<` implies `≤`. -/
private theorem dle_of_lt {a b : Dyadic} (h : a < b) : a ≤ b :=
  Dyadic.toRat_le_toRat_iff.mp (le_of_lt (Dyadic.toRat_lt_toRat_iff.mpr h))

/-- Transitivity of the core dyadic `≤`. -/
private theorem dle_trans {a b c : Dyadic} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  Dyadic.toRat_le_toRat_iff.mp
    (le_trans (Dyadic.toRat_le_toRat_iff.mpr h1) (Dyadic.toRat_le_toRat_iff.mpr h2))

/-- `sturmVarAt` is antitone in the point: the count over `(a, b]` is a
nonnegative cardinality, so the variation at `b` is at most the one at `a`. -/
private theorem sturmVarAt_le (hdeg : 1 ≤ (p.degree?).getD 0)
    (hp : Hex.ZPoly.SquareFreeRat p) {a b : Dyadic} (hab : a < b) :
    Hex.sturmVarAt (Hex.ZPoly.sturmChain p) b
      ≤ Hex.sturmVarAt (Hex.ZPoly.sturmChain p) a := by
  have h := sturmCount_eq_card_roots p hdeg hp ⟨a, b, hab⟩
  have hid : Hex.sturmCount p ⟨a, b, hab⟩
      = (Hex.sturmVarAt (Hex.ZPoly.sturmChain p) a : ℤ)
        - Hex.sturmVarAt (Hex.ZPoly.sturmChain p) b := rfl
  rw [hid] at h
  omega

/-- A real root of the real cast is a complex root of the complex cast. -/
private theorem isRoot_toPolyℂ {r : ℝ} (hr : (toPolyℝ p).IsRoot r) :
    (toPolyℂ p).IsRoot (r : ℂ) := by
  have hcomp : (algebraMap ℝ ℂ).comp (Int.castRingHom ℝ) = Int.castRingHom ℂ :=
    RingHom.ext_int _ _
  have hmap : toPolyℂ p = (toPolyℝ p).map (algebraMap ℝ ℂ) := by
    show (HexPolyZMathlib.toPolynomial p).map (Int.castRingHom ℂ)
        = ((HexPolyZMathlib.toPolynomial p).map (Int.castRingHom ℝ)).map (algebraMap ℝ ℂ)
    rw [Polynomial.map_map, hcomp]
  rw [hmap]
  have h2 : Polynomial.IsRoot ((toPolyℝ p).map (algebraMap ℝ ℂ)) (algebraMap ℝ ℂ r) := hr.map
  simpa using h2

/-- **Separation caps the count.** An interval no wider than `2^(−sepPrec p)`
holds at most one real root of a positive-degree squarefree `p` (two distinct
real roots are more than `4·2^(−sepPrec p)` apart by `sepPrec_separates'`), so
its exact Sturm count is at most `1`. -/
private theorem sturmCount_le_one (hdeg : 1 ≤ (p.degree?).getD 0)
    (hp : Hex.ZPoly.SquareFreeRat p) (J : Hex.DyadicInterval)
    (hw : Dyadic.toReal J.upper - Dyadic.toReal J.lower
      ≤ (2 : ℝ) ^ (-(Hex.sepPrec p : ℤ))) :
    Hex.sturmCount p J ≤ 1 := by
  have hp0 : p ≠ 0 := by
    intro hh; rw [hh] at hdeg; simp only [Hex.DensePoly.degree?_zero_getD] at hdeg; omega
  rw [sturmCount_eq_card_roots p hdeg hp J]
  set M := (toPolyℝ p).roots.filter
      (fun r => Dyadic.toReal J.lower < r ∧ r ≤ Dyadic.toReal J.upper) with hMdef
  suffices h : M.card ≤ 1 by exact_mod_cast h
  by_contra h2
  have hnodup : M.Nodup := by
    rw [hMdef]
    exact (Polynomial.nodup_roots
      (separable_toPolyℝ p ((squareFreeRat_iff p hp0).mp hp))).filter _
  have hfin : 1 < M.toFinset.card := by
    rw [Multiset.toFinset_card_of_nodup hnodup]; omega
  obtain ⟨r₁, hr₁, r₂, hr₂, hne⟩ := Finset.one_lt_card.mp hfin
  rw [Multiset.mem_toFinset, hMdef, Multiset.mem_filter] at hr₁ hr₂
  obtain ⟨hr₁roots, hr₁lo, hr₁hi⟩ := hr₁
  obtain ⟨hr₂roots, hr₂lo, hr₂hi⟩ := hr₂
  have hroot₁ : (toPolyℝ p).IsRoot r₁ := (Polynomial.mem_roots'.mp hr₁roots).2
  have hroot₂ : (toPolyℝ p).IsRoot r₂ := (Polynomial.mem_roots'.mp hr₂roots).2
  have hsep := sepPrec_separates' p hp0 hp (r₁ : ℂ) (r₂ : ℂ)
    (isRoot_toPolyℂ hroot₁) (isRoot_toPolyℂ hroot₂)
    (fun h => hne (by exact_mod_cast h))
  have hnorm : ‖(r₁ : ℂ) - (r₂ : ℂ)‖ = |r₁ - r₂| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have habs : |r₁ - r₂| < Dyadic.toReal J.upper - Dyadic.toReal J.lower :=
    abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(Hex.sepPrec p : ℤ)) := by positivity
  rw [hnorm] at hsep
  linarith

/-- **The `sturmVisit` worklist drains, ordered and count-exact.** For truthful
memoised endpoint counts (`vlo = sturmVarAt chain lo`, `vhi = sturmVarAt chain hi`)
on a nonempty interval whose width is within the depth budget
(`toReal hi − toReal lo ≤ 2^(depth − sepPrec p)`), `sturmVisit` returns `some arr`
where `arr` is an ordered array of `arr.size = vlo − vhi` isolations, each with its
interval inside `(lo, hi]`.

Structural induction on `depth`:

* **Drain / non-`none`.** The only `none` branch is `count ≥ 2` at `depth = 0`.
  At the budget `depth = 0` the width is `≤ 2^(−sepPrec p)`, below the real
  root-gap `4·2^(−sepPrec p)` from `sepPrec_separates'` (via
  `sturmCount_le_one`), so the interval holds `≤ 1` root and
  `count = vlo − vhi ≤ 1` — the `count ≥ 2` branch is never entered. A bisection
  step halves the width, so both children satisfy the budget at `depth − 1`, and
  their memoised midpoint count is truthful by construction; the induction
  hypothesis drains both.
* **Count exactness.** The count-`0`/count-`1` leaves emit `0`/`1` isolations,
  matching `vlo − vhi`. A bisection telescopes: `vlo ≥ vmid ≥ vhi`
  (`sturmVarAt_le`) and `(vlo − vmid) + (vmid − vhi) = vlo − vhi`.
* **Ordering / containment.** The count-`1` leaf emits `(lo, hi]` itself. A
  bisection emits `left ++ right` with every left interval's upper `≤ mid` and
  every right interval's lower `≥ mid`, so the concatenation stays sorted and
  inside `(lo, hi]`. -/
private theorem sturmVisit_spec (hdeg : 1 ≤ (p.degree?).getD 0)
    (hp : Hex.ZPoly.SquareFreeRat p) :
    ∀ (depth : Nat) (lo hi : Dyadic) (vlo vhi : Nat),
      vlo = Hex.sturmVarAt (Hex.ZPoly.sturmChain p) lo →
      vhi = Hex.sturmVarAt (Hex.ZPoly.sturmChain p) hi →
      lo < hi →
      Dyadic.toReal hi - Dyadic.toReal lo ≤ (2 : ℝ) ^ ((depth : ℤ) - (Hex.sepPrec p : ℤ)) →
      ∃ arr : Array (Hex.RealRootIsolation p),
        Hex.sturmVisit p (Hex.ZPoly.sturmChain p) rfl depth lo hi vlo vhi = some arr ∧
        arr.size = vlo - vhi ∧
        (∀ i j : Fin arr.size, i < j → arr[i].interval.upper ≤ arr[j].interval.lower) ∧
        (∀ I ∈ arr, lo ≤ I.interval.lower) ∧ (∀ I ∈ arr, I.interval.upper ≤ hi) := by
  intro depth
  induction depth with
  | zero =>
    intro lo hi vlo vhi hvlo hvhi hlt hw
    subst hvlo; subst hvhi
    simp only [Nat.cast_zero, zero_sub] at hw
    have hunf : Hex.sturmVisit p (Hex.ZPoly.sturmChain p) rfl 0 lo hi
        (Hex.sturmVarAt (Hex.ZPoly.sturmChain p) lo)
        (Hex.sturmVarAt (Hex.ZPoly.sturmChain p) hi)
        = (if Hex.sturmVarAt (Hex.ZPoly.sturmChain p) lo
              = Hex.sturmVarAt (Hex.ZPoly.sturmChain p) hi then some #[]
           else if Hex.sturmVarAt (Hex.ZPoly.sturmChain p) lo
              = Hex.sturmVarAt (Hex.ZPoly.sturmChain p) hi + 1 then
             (if hlt' : lo < hi then
                (if h : (Hex.sturmVarAt (Hex.ZPoly.sturmChain p) lo : Int)
                    - Hex.sturmVarAt (Hex.ZPoly.sturmChain p) hi = 1 then
                  some #[⟨⟨lo, hi, hlt'⟩, h⟩]
                else none)
              else none)
           else none) := rfl
    by_cases h0 : Hex.sturmVarAt (Hex.ZPoly.sturmChain p) lo
        = Hex.sturmVarAt (Hex.ZPoly.sturmChain p) hi
    · refine ⟨#[], by rw [hunf, if_pos h0], by simp [h0], ?_, ?_, ?_⟩
      · intro i j hij; exact absurd i.isLt (by simp)
      · intro I hI; simp at hI
      · intro I hI; simp at hI
    · by_cases h1 : Hex.sturmVarAt (Hex.ZPoly.sturmChain p) lo
          = Hex.sturmVarAt (Hex.ZPoly.sturmChain p) hi + 1
      · have hraw : (Hex.sturmVarAt (Hex.ZPoly.sturmChain p) lo : Int)
            - Hex.sturmVarAt (Hex.ZPoly.sturmChain p) hi = 1 := by omega
        refine ⟨#[⟨⟨lo, hi, hlt⟩, hraw⟩],
          by rw [hunf, if_neg h0, if_pos h1, dif_pos hlt, dif_pos hraw],
          by simp [h1], ?_, ?_, ?_⟩
        · intro i j hij
          have hi1 : (i : ℕ) < 1 := i.isLt
          have hj1 : (j : ℕ) < 1 := j.isLt
          have hij' : (i : ℕ) < (j : ℕ) := hij
          omega
        · intro I hI
          simp only [List.mem_toArray, List.mem_singleton] at hI
          subst hI
          exact dle_refl lo
        · intro I hI
          simp only [List.mem_toArray, List.mem_singleton] at hI
          subst hI
          exact dle_refl hi
      · -- `count ≥ 2` at depth `0`: refuted by the separation bound.
        exfalso
        have hle := sturmVarAt_le hdeg hp hlt
        have hcle : Hex.sturmCount p ⟨lo, hi, hlt⟩ ≤ 1 := sturmCount_le_one hdeg hp _ hw
        have hcle' : (Hex.sturmVarAt (Hex.ZPoly.sturmChain p) lo : ℤ)
            - Hex.sturmVarAt (Hex.ZPoly.sturmChain p) hi ≤ 1 := hcle
        omega
  | succ d ih =>
    intro lo hi vlo vhi hvlo hvhi hlt hw
    subst hvlo; subst hvhi
    have hunf : Hex.sturmVisit p (Hex.ZPoly.sturmChain p) rfl (d + 1) lo hi
        (Hex.sturmVarAt (Hex.ZPoly.sturmChain p) lo)
        (Hex.sturmVarAt (Hex.ZPoly.sturmChain p) hi)
        = (if Hex.sturmVarAt (Hex.ZPoly.sturmChain p) lo
              = Hex.sturmVarAt (Hex.ZPoly.sturmChain p) hi then some #[]
           else if Hex.sturmVarAt (Hex.ZPoly.sturmChain p) lo
              = Hex.sturmVarAt (Hex.ZPoly.sturmChain p) hi + 1 then
             (if hlt' : lo < hi then
                (if h : (Hex.sturmVarAt (Hex.ZPoly.sturmChain p) lo : Int)
                    - Hex.sturmVarAt (Hex.ZPoly.sturmChain p) hi = 1 then
                  some #[⟨⟨lo, hi, hlt'⟩, h⟩]
                else none)
              else none)
           else
             match Hex.sturmVisit p (Hex.ZPoly.sturmChain p) rfl d
                 lo ((lo + hi) >>> (1 : Int))
                 (Hex.sturmVarAt (Hex.ZPoly.sturmChain p) lo)
                 (Hex.sturmVarAt (Hex.ZPoly.sturmChain p) ((lo + hi) >>> (1 : Int))) with
             | none => none
             | some left =>
               match Hex.sturmVisit p (Hex.ZPoly.sturmChain p) rfl d
                   ((lo + hi) >>> (1 : Int)) hi
                   (Hex.sturmVarAt (Hex.ZPoly.sturmChain p) ((lo + hi) >>> (1 : Int)))
                   (Hex.sturmVarAt (Hex.ZPoly.sturmChain p) hi) with
               | none => none
               | some right => some (left ++ right)) := rfl
    by_cases h0 : Hex.sturmVarAt (Hex.ZPoly.sturmChain p) lo
        = Hex.sturmVarAt (Hex.ZPoly.sturmChain p) hi
    · refine ⟨#[], by rw [hunf, if_pos h0], by simp [h0], ?_, ?_, ?_⟩
      · intro i j hij; exact absurd i.isLt (by simp)
      · intro I hI; simp at hI
      · intro I hI; simp at hI
    · by_cases h1 : Hex.sturmVarAt (Hex.ZPoly.sturmChain p) lo
          = Hex.sturmVarAt (Hex.ZPoly.sturmChain p) hi + 1
      · have hraw : (Hex.sturmVarAt (Hex.ZPoly.sturmChain p) lo : Int)
            - Hex.sturmVarAt (Hex.ZPoly.sturmChain p) hi = 1 := by omega
        refine ⟨#[⟨⟨lo, hi, hlt⟩, hraw⟩],
          by rw [hunf, if_neg h0, if_pos h1, dif_pos hlt, dif_pos hraw],
          by simp [h1], ?_, ?_, ?_⟩
        · intro i j hij
          have hi1 : (i : ℕ) < 1 := i.isLt
          have hj1 : (j : ℕ) < 1 := j.isLt
          have hij' : (i : ℕ) < (j : ℕ) := hij
          omega
        · intro I hI
          simp only [List.mem_toArray, List.mem_singleton] at hI
          subst hI
          exact dle_refl lo
        · intro I hI
          simp only [List.mem_toArray, List.mem_singleton] at hI
          subst hI
          exact dle_refl hi
      · -- Bisection: recurse into the two halves.
        have hlm : lo < (lo + hi) >>> (1 : Int) := lower_lt_midpoint ⟨lo, hi, hlt⟩
        have hmh : (lo + hi) >>> (1 : Int) < hi := midpoint_lt_upper ⟨lo, hi, hlt⟩
        have hmidR : Dyadic.toReal ((lo + hi) >>> (1 : Int))
            = (Dyadic.toReal lo + Dyadic.toReal hi) / 2 := toReal_midpoint ⟨lo, hi, hlt⟩
        have hzp : (2 : ℝ) ^ (((d + 1 : ℕ) : ℤ) - (Hex.sepPrec p : ℤ))
            = 2 * (2 : ℝ) ^ ((d : ℤ) - (Hex.sepPrec p : ℤ)) := by
          rw [show ((d + 1 : ℕ) : ℤ) - (Hex.sepPrec p : ℤ)
              = ((d : ℤ) - (Hex.sepPrec p : ℤ)) + 1 by push_cast; ring,
            zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
          ring
        rw [hzp] at hw
        have hwl : Dyadic.toReal ((lo + hi) >>> (1 : Int)) - Dyadic.toReal lo
            ≤ (2 : ℝ) ^ ((d : ℤ) - (Hex.sepPrec p : ℤ)) := by
          rw [hmidR]; linarith
        have hwr : Dyadic.toReal hi - Dyadic.toReal ((lo + hi) >>> (1 : Int))
            ≤ (2 : ℝ) ^ ((d : ℤ) - (Hex.sepPrec p : ℤ)) := by
          rw [hmidR]; linarith
        obtain ⟨left, hLeq, hLsize, hLord, hLlo, hLhi⟩ :=
          ih lo ((lo + hi) >>> (1 : Int)) _ _ rfl rfl hlm hwl
        obtain ⟨right, hReq, hRsize, hRord, hRlo, hRhi⟩ :=
          ih ((lo + hi) >>> (1 : Int)) hi _ _ rfl rfl hmh hwr
        have hle1 : Hex.sturmVarAt (Hex.ZPoly.sturmChain p) ((lo + hi) >>> (1 : Int))
            ≤ Hex.sturmVarAt (Hex.ZPoly.sturmChain p) lo := sturmVarAt_le hdeg hp hlm
        have hle2 : Hex.sturmVarAt (Hex.ZPoly.sturmChain p) hi
            ≤ Hex.sturmVarAt (Hex.ZPoly.sturmChain p) ((lo + hi) >>> (1 : Int)) :=
          sturmVarAt_le hdeg hp hmh
        refine ⟨left ++ right, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hunf, if_neg h0, if_neg h1, hLeq, hReq]
        · rw [Array.size_append, hLsize, hRsize]
          omega
        · -- The concatenation stays sorted: `left`'s uppers sit below the
          -- midpoint, `right`'s lowers above it.
          intro i j hij
          have hij' : (i : ℕ) < (j : ℕ) := hij
          have hi' : (i : ℕ) < left.size + right.size := i.isLt.trans_eq Array.size_append
          have hj' : (j : ℕ) < left.size + right.size := j.isLt.trans_eq Array.size_append
          by_cases hjL : (j : ℕ) < left.size
          · have hiL : (i : ℕ) < left.size := lt_trans hij' hjL
            rw [Fin.getElem_fin, Fin.getElem_fin, Array.getElem_append_left hiL,
              Array.getElem_append_left hjL]
            exact hLord ⟨(i : ℕ), hiL⟩ ⟨(j : ℕ), hjL⟩ hij'
          · have hjR : left.size ≤ (j : ℕ) := le_of_not_gt hjL
            by_cases hiL : (i : ℕ) < left.size
            · rw [Fin.getElem_fin, Fin.getElem_fin, Array.getElem_append_left hiL,
                Array.getElem_append_right hjR]
              exact dle_trans (hLhi _ (Array.getElem_mem hiL))
                (hRlo _ (Array.getElem_mem (by omega)))
            · have hiR : left.size ≤ (i : ℕ) := le_of_not_gt hiL
              rw [Fin.getElem_fin, Fin.getElem_fin, Array.getElem_append_right hiR,
                Array.getElem_append_right hjR]
              exact hRord ⟨(i : ℕ) - left.size, by omega⟩ ⟨(j : ℕ) - left.size, by omega⟩
                (by simp only [Fin.mk_lt_mk]; omega)
        · intro I hI
          rcases Array.mem_append.mp hI with h | h
          · exact hLlo I h
          · exact dle_trans (dle_of_lt hlm) (hRlo I h)
        · intro I hI
          rcases Array.mem_append.mp hI with h | h
          · exact dle_trans (hLhi I h) (dle_of_lt hmh)
          · exact hRhi I h

/-- The final assembly step succeeds once its two invariants are witnessed. -/
private theorem assemble?_isSome {chain : Array Hex.ZPoly}
    (hchain : chain = Hex.ZPoly.sturmChain p) (arr : Array (Hex.RealRootIsolation p))
    (hord : ∀ i j : Fin arr.size, i < j → arr[i].interval.upper ≤ arr[j].interval.lower)
    (hsize : arr.size = Hex.sturmVarNegInf chain - Hex.sturmVarPosInf chain) :
    (Hex.assemble? p chain hchain arr).isSome := by
  unfold Hex.assemble?
  rw [dif_pos hord, dif_pos hsize]
  rfl

/-- `isolateSturm?` on positive-degree squarefree input is the top `sturmVisit`
run handed to `assemble?`. -/
private theorem isolateSturm?_eq {d : Nat} (hd : p.degree? = some (d + 1))
    (hp : Hex.ZPoly.SquareFreeRat p) :
    Hex.isolateSturm? p =
      (match Hex.sturmVisit p (Hex.ZPoly.sturmChain p) rfl (Hex.isolationDepth p)
          (-(Hex.rootBound p)) (Hex.rootBound p)
          (Hex.sturmVarAt (Hex.ZPoly.sturmChain p) (-(Hex.rootBound p)))
          (Hex.sturmVarAt (Hex.ZPoly.sturmChain p) (Hex.rootBound p)) with
        | none => none
        | some arr => Hex.assemble? p (Hex.ZPoly.sturmChain p) rfl arr) := by
  unfold Hex.isolateSturm?
  simp only [hd]
  rw [if_pos hp]
  rfl

/-! ### Driver completeness -/

/-- The positive-degree core of `isolateSturm?_isSome`: the worklist drains
(`sturmVisit_spec`) and the emitted total matches
`rootCount p = sturmVarNegInf − sturmVarPosInf` (the `±rootBound` gap counts
every root, `sturmVar_neg_pos_sub`), so `assemble?` certifies. -/
private theorem isolateSturm?_isSome_of_degree_pos (hdeg : 1 ≤ (p.degree?).getD 0)
    (hp : Hex.ZPoly.SquareFreeRat p) : (Hex.isolateSturm? p).isSome := by
  obtain ⟨d, hd⟩ : ∃ d, p.degree? = some (d + 1) := by
    rcases hh : p.degree? with _ | n
    · rw [hh] at hdeg; simp at hdeg
    · rcases n with _ | m
      · rw [hh] at hdeg; simp at hdeg
      · exact ⟨m, rfl⟩
  have hlt : -(Hex.rootBound p) < Hex.rootBound p := neg_rootBound_lt_rootBound p
  obtain ⟨arr, hvisit, hsize, hord, -, -⟩ :=
    sturmVisit_spec hdeg hp (Hex.isolationDepth p) (-(Hex.rootBound p)) (Hex.rootBound p)
      (Hex.sturmVarAt (Hex.ZPoly.sturmChain p) (-(Hex.rootBound p)))
      (Hex.sturmVarAt (Hex.ZPoly.sturmChain p) (Hex.rootBound p)) rfl rfl hlt
      (initial_width_le p hdeg)
  have hInt := sturmVar_neg_pos_sub hdeg hp
  have hsize' : arr.size = Hex.sturmVarNegInf (Hex.ZPoly.sturmChain p)
      - Hex.sturmVarPosInf (Hex.ZPoly.sturmChain p) := by
    have hrc : Hex.rootCount p = Hex.sturmVarNegInf (Hex.ZPoly.sturmChain p)
        - Hex.sturmVarPosInf (Hex.ZPoly.sturmChain p) := rfl
    rw [hsize, ← hrc]; omega
  rw [isolateSturm?_eq hd hp, hvisit]
  exact assemble?_isSome rfl arr hord hsize'

/-- The Sturm engine on a nonzero constant: the driver's `some 0` branch hands
`assemble?` the empty emission array, and the empty chain certifies
`rootCount p = 0` (`sturmVarNegInf #[] − sturmVarPosInf #[] = 0`). -/
private theorem isolateSturm?_isSome_of_degree_zero (hd : p.degree? = some 0) :
    (Hex.isolateSturm? p).isSome := by
  have heq : Hex.isolateSturm? p = Hex.assemble? p (Hex.ZPoly.sturmChain p) rfl #[] := by
    unfold Hex.isolateSturm?
    rw [hd]
  have hchain0 : Hex.ZPoly.sturmChain p = #[] := by
    unfold Hex.ZPoly.sturmChain
    rw [hd]
    rfl
  rw [heq]
  refine assemble?_isSome rfl #[] ?_ ?_
  · intro i j hij
    exact absurd i.isLt (by simp)
  · rw [hchain0]
    rfl

/-- **The Sturm engine succeeds on nonzero squarefree input.** Positive degree
is the real content (`isolateSturm?_isSome_of_degree_pos`); a nonzero constant
certifies through the empty chain.

The SPEC states this with only `SquareFreeRat p`; the `p ≠ 0` hypothesis is
added because `SquareFreeRat 0` is vacuous while `isolateSturm? 0 = none`. -/
theorem isolateSturm?_isSome (p : Hex.ZPoly) (hp0 : p ≠ 0)
    (hp : Hex.ZPoly.SquareFreeRat p) : (Hex.isolateSturm? p).isSome := by
  rcases hd : p.degree? with _ | n
  · exact absurd hd (degree?_ne_none hp0)
  · rcases n with _ | n
    · exact isolateSturm?_isSome_of_degree_zero hd
    · exact isolateSturm?_isSome_of_degree_pos (by simp [hd]) hp

/-- **The top-level driver succeeds on nonzero squarefree input.** A one-liner
over `isolateSturm?_isSome`: `isolate?` keeps whichever engine's certified
output arrives first, and the Sturm engine always has one. -/
theorem isolate?_isSome (p : Hex.ZPoly) (hp0 : p ≠ 0)
    (hp : Hex.ZPoly.SquareFreeRat p) : (Hex.isolate? p).isSome := by
  have hs := isolateSturm?_isSome p hp0 hp
  unfold Hex.isolate?
  cases hD : Hex.isolateDescartes? p with
  | some a => rfl
  | none => rw [hD] at *; simpa using hs

end

end HexRealRootsMathlib
