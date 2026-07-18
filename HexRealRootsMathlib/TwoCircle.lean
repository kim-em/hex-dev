/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib
public import HexRealRootsMathlib.MobiusCorrespond
public import HexRealRootsMathlib.DescartesParity
public import HexRealRootsMathlib.TwoCircleRegion
public import HexRealRootsMathlib.TwoCircleSector
public import HexRealRootsMathlib.Drivers
public import HexRealRoots.IsolateDescartes
-- `import all` on the executable modules so the non-`@[expose]` bodies of
-- `descartesVisit`, `isolateDescartes?`, `mobiusTransform`, `descartesVar`,
-- `sturmVarAt`, `sturmChain`, `evalDyadic`, `dyadicSign`, `rootBound`,
-- `sepPrec`, `isolationDepth`, and `assemble?` unfold here.
import all HexRealRootsMathlib.Separation
import all HexRealRoots.Basic
import all HexRealRoots.Chain
import all HexRealRoots.Var
import all HexRealRoots.Mobius
import all HexRealRoots.Prec
import all HexRealRoots.IsolateDescartes

public section

/-!
# The Descartes engine never falls back (the two-circle termination theorem)

This module proves `isolateDescartes?_isSome`: the *Descartes* isolation engine
alone returns `some` on every nonzero square-free input, so the runtime never
needs the Sturm fallback. It is the last theorem of `HexRealRootsMathlib`, and
with it the companion is fully `sorry`-free.

## What the two-circle theorem actually says

The classical statement is **not** a general count bound. It is *λ-graded*
(Obreschkoff 1963; modern treatments Krandick–Mehlhorn 2006, Eigenwillig 2008):
if all but `λ` complex roots of a real polynomial lie in the closed sector of
half-angle `π/(λ+2)` about the negative real axis (equivalently, at most `λ`
roots lie outside), then the coefficient sequence has at most `λ` sign
variations. The naive reading "variation count ≤ number of roots in the
two-circle region" is **false**: `(X²+X+1)·(X²−(3/2)X+1)` has four sign
variations while only two of its roots lie outside the sector (the
counterexample recorded in `TwoCircleSector.lean`).

We need only the two lowest graded cases, `λ ∈ {0, 1}`, and both are already
proven: `Polynomial.signVariations_le_one_of_sector` (`TwoCircleSector.lean`) is
the `λ = 1` sector bound via Hoggar log-concavity, and its `λ = 0` corollary.

## The proof route

At a node `(lo, hi]` write `V` for the Descartes variation count of the Möbius
transform. `descartesVar_mobiusTransform` identifies `V` with
`signVariations (mobiusPoly n a b (toPolyℝ p))` (`n = deg p`,
`a = toReal lo`, `b = toReal hi`); `countP_roots_mobiusPoly` turns the count of
*positive* transform-roots into the count of `p`-roots in the open interval
`(a, b)`; and the Descartes parity exports pin that count exactly when `V ∈
{0, 1}`. Together with the exact endpoint test `p(b) = 0`
(`sign_dyadicSign`/`toReal_evalDyadic`), the half-open Sturm count on `(a, b]` is
computed exactly, so every candidate row certifies (Sturm count `1`) and every
discard row emits `#[]` (Sturm count `0`) — *node truthfulness*, needing no width
budget.

At the depth budget (interval width `≤ 2^{−sepPrec p}`) the two bisecting rows
are refuted:

* `V = 1 ∧ p(b) = 0` would put two real roots — one interior, plus `b` — in
  `(a, b]`, a Sturm count of `2`, contradicting `sturmCount_le_one`.
* `V ≥ 2` triggers the sector bound: `≥ 2` transform-roots lie outside the
  sector, hence (`roots_mobiusPoly` on `ℂ`, `not_inTwoCircle_iff_mem_sector`)
  `≥ 2` distinct roots of `p` lie inside the two-circle region, which is enclosed
  in a ball of radius `√3·(b−a)/2` (`dist_le`); two such roots are within
  `√3·2^{−sepPrec p} < 4·2^{−sepPrec p}`, contradicting the Mahler separation
  bound `sepPrec_separates'`. Square-freeness (`separable_toPolyℝ` ⇒ nodup)
  supplies distinctness.

The worklist therefore drains at `isolationDepth p`, mirroring the Sturm engine's
`sturmVisit_spec`/`isolateSturm?_isSome` in `Drivers.lean`.
-/

namespace HexRealRootsMathlib

open Polynomial

noncomputable section

variable {p : Hex.ZPoly}

/-! ### The exact endpoint test -/

/-- The executable endpoint test `dyadicSign (p(hi)) == 0` decides whether `hi`
is a real root of `toPolyℝ p`: the exact dyadic evaluation has the same sign as
the real evaluation (`sign_dyadicSign`, `toReal_evalDyadic`), so it is zero
exactly at a root. -/
theorem bZero_iff (hi : Dyadic) :
    (Hex.dyadicSign (p.evalDyadic hi) == 0) = true
      ↔ (toPolyℝ p).IsRoot (Dyadic.toReal hi) := by
  rw [beq_iff_eq]
  have hs : SignType.sign ((Hex.dyadicSign (p.evalDyadic hi) : ℝ))
      = SignType.sign (Dyadic.toReal (p.evalDyadic hi)) := sign_dyadicSign _
  constructor
  · intro h
    rw [h] at hs
    simp only [Int.cast_zero, sign_zero] at hs
    have h0 : Dyadic.toReal (p.evalDyadic hi) = 0 := sign_eq_zero_iff.mp hs.symm
    rw [toReal_evalDyadic] at h0
    exact h0
  · intro h
    have h0 : Dyadic.toReal (p.evalDyadic hi) = 0 := by rw [toReal_evalDyadic]; exact h
    rw [h0] at hs
    simp only [sign_zero] at hs
    have : ((Hex.dyadicSign (p.evalDyadic hi) : Int) : ℝ) = 0 := sign_eq_zero_iff.mp hs
    exact_mod_cast this

/-! ### The exact node count -/

/-- **Node count.** For positive-degree square-free `p` and `lo < hi`, the exact
Sturm count on `(lo, hi]` splits as the number of positive roots of the Möbius
transform (= the `p`-roots in the open interval `(a, b)`) plus the endpoint
indicator `[p(hi) = 0]`. No width budget is needed: the count is exact. -/
theorem descartes_node_count (hdeg : 1 ≤ (p.degree?).getD 0)
    (hp : Hex.ZPoly.SquareFreeRat p) {lo hi : Dyadic} (hlt : lo < hi) :
    (Hex.sturmVarAt (Hex.ZPoly.sturmChain p) lo : Int)
        - Hex.sturmVarAt (Hex.ZPoly.sturmChain p) hi
      = ((mobiusPoly ((p.degree?).getD 0) (Dyadic.toReal lo) (Dyadic.toReal hi)
            (toPolyℝ p)).roots.countP (0 < ·) : Int)
        + (if (toPolyℝ p).IsRoot (Dyadic.toReal hi) then 1 else 0) := by
  classical
  have hp0 : p ≠ 0 := by
    intro hh; rw [hh] at hdeg; simp only [Hex.DensePoly.degree?_zero_getD] at hdeg; omega
  have hP0 : toPolyℝ p ≠ 0 := fun h => hp0 (toPolyℝ_eq_zero_iff.mp h)
  have hab : Dyadic.toReal lo < Dyadic.toReal hi := toReal_lt_toReal_iff.mpr hlt
  have hdeg' : (toPolyℝ p).natDegree ≤ (p.degree?).getD 0 := le_of_eq (natDegree_toPolyℝ p)
  have hsep : (toPolyℝ p).Separable := separable_toPolyℝ p ((squareFreeRat_iff p hp0).mp hp)
  have hnodup : (toPolyℝ p).roots.Nodup := nodup_roots hsep
  set a := Dyadic.toReal lo with ha
  set b := Dyadic.toReal hi with hb
  -- The half-open Sturm count is the card of the filtered root multiset.
  have hd : (Hex.sturmVarAt (Hex.ZPoly.sturmChain p) lo : Int)
      - Hex.sturmVarAt (Hex.ZPoly.sturmChain p) hi
      = (((toPolyℝ p).roots.filter (fun r => a < r ∧ r ≤ b)).card : ℤ) :=
    sturmCount_eq_card_roots p hdeg hp ⟨lo, hi, hlt⟩
  rw [hd, countP_roots_mobiusPoly hab hP0 hdeg', Multiset.countP_eq_card_filter]
  -- Split the half-open filter into the open filter plus the `{b}` filter.
  have hend : ((toPolyℝ p).roots.filter (fun r => r = b)).card
      = if (toPolyℝ p).IsRoot b then 1 else 0 := by
    rw [Multiset.filter_eq', Multiset.card_replicate]
    by_cases hbroot : (toPolyℝ p).IsRoot b
    · rw [if_pos hbroot,
        Multiset.count_eq_one_of_mem hnodup (Polynomial.mem_roots'.mpr ⟨hP0, hbroot⟩)]
    · rw [if_neg hbroot, Multiset.count_eq_zero.mpr
        (fun hm => hbroot (Polynomial.mem_roots'.mp hm).2)]
  have hsplit : ((toPolyℝ p).roots.filter (fun r => a < r ∧ r ≤ b)).card
      = ((toPolyℝ p).roots.filter (fun r => a < r ∧ r < b)).card
        + (if (toPolyℝ p).IsRoot b then 1 else 0) := by
    have hadd := Multiset.filter_add_filter
        (fun r : ℝ => r = b) (toPolyℝ p).roots (p := fun r : ℝ => a < r ∧ r < b)
    have e1 : (toPolyℝ p).roots.filter (fun r => (a < r ∧ r < b) ∨ r = b)
        = (toPolyℝ p).roots.filter (fun r => a < r ∧ r ≤ b) := by
      refine Multiset.filter_congr (fun r _ => ?_)
      constructor
      · rintro (⟨h1, h2⟩ | rfl)
        · exact ⟨h1, le_of_lt h2⟩
        · exact ⟨hab, le_refl _⟩
      · rintro ⟨h1, h2⟩
        rcases lt_or_eq_of_le h2 with h | h
        · exact Or.inl ⟨h1, h⟩
        · exact Or.inr h
    have e2 : (toPolyℝ p).roots.filter (fun r => (a < r ∧ r < b) ∧ r = b) = 0 := by
      rw [Multiset.filter_eq_nil]
      rintro r _ ⟨⟨_, hlt'⟩, rfl⟩
      exact lt_irrefl _ hlt'
    rw [e1, e2, add_zero] at hadd
    have hcard := congrArg Multiset.card hadd
    rw [Multiset.card_add, hend] at hcard
    omega
  rw [hsplit]
  push_cast
  ring

/-! ### Node truthfulness -/

/-- The Descartes dispatch Boolean at a node. -/
private def dispatchC (p : Hex.ZPoly) (lo hi : Dyadic) (hlt : lo < hi) : Bool :=
  (Hex.descartesVar (Hex.mobiusTransform p ⟨lo, hi, hlt⟩) == 0
      && (Hex.dyadicSign (p.evalDyadic hi) == 0))
    || (Hex.descartesVar (Hex.mobiusTransform p ⟨lo, hi, hlt⟩) == 1
      && !(Hex.dyadicSign (p.evalDyadic hi) == 0))

/-- **Candidate rows certify.** When the dispatch Boolean is `true` (either
`V = 0 ∧ p(hi) = 0` or `V = 1 ∧ p(hi) ≠ 0`) the exact Sturm count is `1`, so the
node's certification guard succeeds. -/
private theorem node_candidate (hdeg : 1 ≤ (p.degree?).getD 0)
    (hp : Hex.ZPoly.SquareFreeRat p) {lo hi : Dyadic} (hlt : lo < hi)
    (hC : dispatchC p lo hi hlt = true) :
    (Hex.sturmVarAt (Hex.ZPoly.sturmChain p) lo : Int)
      - Hex.sturmVarAt (Hex.ZPoly.sturmChain p) hi = 1 := by
  have hp0 : p ≠ 0 := by
    intro hh; rw [hh] at hdeg; simp only [Hex.DensePoly.degree?_zero_getD] at hdeg; omega
  have hP0 : toPolyℝ p ≠ 0 := fun h => hp0 (toPolyℝ_eq_zero_iff.mp h)
  have hab : Dyadic.toReal lo < Dyadic.toReal hi := toReal_lt_toReal_iff.mpr hlt
  set M := mobiusPoly ((p.degree?).getD 0) (Dyadic.toReal lo) (Dyadic.toReal hi) (toPolyℝ p) with hM
  have hMne : M ≠ 0 := mobiusPoly_ne_zero_of_ne (ne_of_lt hab) hP0
  have hV : Hex.descartesVar (Hex.mobiusTransform p ⟨lo, hi, hlt⟩) = Polynomial.signVariations M :=
    descartesVar_mobiusTransform p ⟨lo, hi, hlt⟩ hdeg
  have hcnt := descartes_node_count hdeg hp hlt
  rw [← hM] at hcnt
  unfold dispatchC at hC
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hC
  rcases hC with ⟨hV0, hbz⟩ | ⟨hV1, hbz⟩
  · have hSV0 : Polynomial.signVariations M = 0 := by rw [← hV]; simpa using hV0
    have hcp := Polynomial.countP_pos_eq_zero_of_signVariations_eq_zero hMne hSV0
    have hroot : (toPolyℝ p).IsRoot (Dyadic.toReal hi) := (bZero_iff hi).mp hbz
    rw [hcnt, hcp, if_pos hroot]; norm_num
  · have hSV1 : Polynomial.signVariations M = 1 := by rw [← hV]; simpa using hV1
    have hcp := Polynomial.countP_pos_eq_one_of_signVariations_eq_one hMne hSV1
    have hbzf : (Hex.dyadicSign (p.evalDyadic hi) == 0) = false := by simpa using hbz
    have hnroot : ¬ (toPolyℝ p).IsRoot (Dyadic.toReal hi) := fun hr => by
      rw [(bZero_iff hi).mpr hr] at hbzf; exact absurd hbzf (by decide)
    rw [hcnt, hcp, if_neg hnroot]; norm_num

/-- **Discard rows are truthful.** When the dispatch Boolean is `false` with
`V = 0` (so `p(hi) ≠ 0`), the exact Sturm count is `0`, so the node's emitted
`#[]` matches. -/
private theorem node_discard (hdeg : 1 ≤ (p.degree?).getD 0)
    (hp : Hex.ZPoly.SquareFreeRat p) {lo hi : Dyadic} (hlt : lo < hi)
    (hC : dispatchC p lo hi hlt = false)
    (hV0 : Hex.descartesVar (Hex.mobiusTransform p ⟨lo, hi, hlt⟩) = 0) :
    (Hex.sturmVarAt (Hex.ZPoly.sturmChain p) lo : Int)
      - Hex.sturmVarAt (Hex.ZPoly.sturmChain p) hi = 0 := by
  have hp0 : p ≠ 0 := by
    intro hh; rw [hh] at hdeg; simp only [Hex.DensePoly.degree?_zero_getD] at hdeg; omega
  have hP0 : toPolyℝ p ≠ 0 := fun h => hp0 (toPolyℝ_eq_zero_iff.mp h)
  have hab : Dyadic.toReal lo < Dyadic.toReal hi := toReal_lt_toReal_iff.mpr hlt
  set M := mobiusPoly ((p.degree?).getD 0) (Dyadic.toReal lo) (Dyadic.toReal hi) (toPolyℝ p) with hM
  have hMne : M ≠ 0 := mobiusPoly_ne_zero_of_ne (ne_of_lt hab) hP0
  have hV : Hex.descartesVar (Hex.mobiusTransform p ⟨lo, hi, hlt⟩) = Polynomial.signVariations M :=
    descartesVar_mobiusTransform p ⟨lo, hi, hlt⟩ hdeg
  have hcnt := descartes_node_count hdeg hp hlt
  rw [← hM] at hcnt
  -- `V = 0` collapses the dispatch to `bZero`, and `hC = false` forces `bZero = false`.
  have hbzf : (Hex.dyadicSign (p.evalDyadic hi) == 0) = false := by
    unfold dispatchC at hC
    rw [hV0] at hC
    simpa using hC
  have hnroot : ¬ (toPolyℝ p).IsRoot (Dyadic.toReal hi) := fun hr => by
    rw [(bZero_iff hi).mpr hr] at hbzf; exact absurd hbzf (by decide)
  have hSV0 : Polynomial.signVariations M = 0 := by rw [← hV]; exact hV0
  have hcp := Polynomial.countP_pos_eq_zero_of_signVariations_eq_zero hMne hSV0
  rw [hcnt, hcp, if_neg hnroot]; norm_num

/-! ### Depth-budget refutation of the bisecting rows -/

/-- The real cast of `toPolyℝ p` to `ℂ` is `toPolyℂ p`. -/
private theorem map_toPolyℝ_eq_toPolyℂ (p : Hex.ZPoly) :
    (toPolyℝ p).map (algebraMap ℝ ℂ) = toPolyℂ p := by
  ext n
  rw [Polynomial.coeff_map, coeff_toPolyℝ, coeff_toPolyℂ, Complex.coe_algebraMap]
  push_cast; ring

/-- `toPolyℂ p` is separable for square-free `p`, hence has nodup roots. -/
private theorem nodup_roots_toPolyℂ (hp0 : p ≠ 0) (hp : Hex.ZPoly.SquareFreeRat p) :
    (toPolyℂ p).roots.Nodup := by
  have hsepℝ : (toPolyℝ p).Separable := separable_toPolyℝ p ((squareFreeRat_iff p hp0).mp hp)
  have hsepℂ : (toPolyℂ p).Separable := by
    rw [← map_toPolyℝ_eq_toPolyℂ]; exact hsepℝ.map
  exact nodup_roots hsepℂ

/-- **The `V ≥ 2` row is impossible at the depth budget.** Two or more
transform-roots outside the sector correspond to two distinct roots of `p` inside
the two-circle region, which are closer than `4·2^{−sepPrec p}`, contradicting
the Mahler separation bound. -/
theorem bisect_refute_sector (hdeg : 1 ≤ (p.degree?).getD 0)
    (hp : Hex.ZPoly.SquareFreeRat p) {lo hi : Dyadic} (hlt : lo < hi)
    (hw : Dyadic.toReal hi - Dyadic.toReal lo ≤ (2 : ℝ) ^ (-(Hex.sepPrec p : ℤ)))
    (hV2 : 2 ≤ Hex.descartesVar (Hex.mobiusTransform p ⟨lo, hi, hlt⟩)) :
    False := by
  classical
  have hp0 : p ≠ 0 := by
    intro hh; rw [hh] at hdeg; simp only [Hex.DensePoly.degree?_zero_getD] at hdeg; omega
  have hP0 : toPolyℝ p ≠ 0 := fun h => hp0 (toPolyℝ_eq_zero_iff.mp h)
  have hPℂ0 : toPolyℂ p ≠ 0 := fun h => hp0 (by
    have : toPolyℝ p = 0 := by
      rw [← map_toPolyℝ_eq_toPolyℂ] at h
      exact (Polynomial.map_eq_zero_iff (RingHom.injective (algebraMap ℝ ℂ))).mp h
    exact toPolyℝ_eq_zero_iff.mp this)
  set a := Dyadic.toReal lo with ha
  set b := Dyadic.toReal hi with hb
  have hab : a < b := toReal_lt_toReal_iff.mpr hlt
  have habℂ : (a : ℂ) ≠ (b : ℂ) := fun h => (ne_of_lt hab) (Complex.ofReal_inj.mp h)
  set M := mobiusPoly ((p.degree?).getD 0) a b (toPolyℝ p) with hM
  have hMne : M ≠ 0 := mobiusPoly_ne_zero_of_ne (ne_of_lt hab) hP0
  have hV2M : 2 ≤ Polynomial.signVariations M := by
    have h := descartesVar_mobiusTransform p ⟨lo, hi, hlt⟩ hdeg
    rw [show (⟨lo, hi, hlt⟩ : Hex.DyadicInterval).lower = lo from rfl,
      show (⟨lo, hi, hlt⟩ : Hex.DyadicInterval).upper = hi from rfl, ← ha, ← hb] at h
    rw [hM]; omega
  -- `≥ 2` transform-roots lie outside the sector.
  have hcount2 : 2 ≤ (M.map (algebraMap ℝ ℂ)).roots.countP (· ∉ Polynomial.sector) := by
    by_contra h
    have hle := Polynomial.signVariations_le_one_of_sector hMne (by omega)
    omega
  -- Identify the complex transform with the abstract complex Möbius polynomial.
  have hMmap : M.map (algebraMap ℝ ℂ)
      = mobiusPoly (toPolyℂ p).natDegree (a : ℂ) (b : ℂ) (toPolyℂ p) := by
    rw [natDegree_toPolyℂ, hM, mobiusPoly_map, map_toPolyℝ_eq_toPolyℂ, Complex.coe_algebraMap]
  rw [hMmap, roots_mobiusPoly habℂ hPℂ0, Multiset.countP_map] at hcount2
  -- Two distinct region roots.
  set T := ((toPolyℂ p).roots.filter (· ≠ (b : ℂ))).filter
      (fun w => (w - (a : ℂ)) / ((b : ℂ) - w) ∉ Polynomial.sector) with hT
  have hnodupℂ := nodup_roots_toPolyℂ hp0 hp
  have hnodupT : T.Nodup := (hnodupℂ.filter _).filter _
  have hcardT : 2 ≤ T.card := hcount2
  have hfin : 1 < T.toFinset.card := by
    rw [Multiset.toFinset_card_of_nodup hnodupT]; omega
  obtain ⟨w₁, hw₁, w₂, hw₂, hne⟩ := Finset.one_lt_card.mp hfin
  rw [Multiset.mem_toFinset, hT, Multiset.mem_filter, Multiset.mem_filter] at hw₁ hw₂
  obtain ⟨⟨hw₁roots, hw₁neb⟩, hw₁sec⟩ := hw₁
  obtain ⟨⟨hw₂roots, hw₂neb⟩, hw₂sec⟩ := hw₂
  have hIn₁ : TwoCircle.InTwoCircle a b w₁ := by
    by_contra hcon
    have hmem := (TwoCircle.not_inTwoCircle_iff_mem_sector a b w₁ hw₁neb).mp hcon
    exact hw₁sec (Polynomial.mem_sector.mpr (TwoCircle.mem_sector.mp hmem))
  have hIn₂ : TwoCircle.InTwoCircle a b w₂ := by
    by_contra hcon
    have hmem := (TwoCircle.not_inTwoCircle_iff_mem_sector a b w₂ hw₂neb).mp hcon
    exact hw₂sec (Polynomial.mem_sector.mpr (TwoCircle.mem_sector.mp hmem))
  have hr₁ : (toPolyℂ p).IsRoot w₁ := (Polynomial.mem_roots'.mp hw₁roots).2
  have hr₂ : (toPolyℂ p).IsRoot w₂ := (Polynomial.mem_roots'.mp hw₂roots).2
  -- Distance bound from the ball enclosure.
  have hd₁ := TwoCircle.dist_le a b w₁ hab.le hIn₁
  have hd₂ := TwoCircle.dist_le a b w₂ hab.le hIn₂
  have hdist : dist w₁ w₂ ≤ Real.sqrt 3 * (b - a) := by
    have htri := dist_triangle w₁ (((a + b) / 2 : ℝ) : ℂ) w₂
    have hd₂' : dist (((a + b) / 2 : ℝ) : ℂ) w₂ ≤ Real.sqrt 3 * (b - a) / 2 := by
      rw [dist_comm]; exact hd₂
    linarith [htri, hd₁, hd₂']
  have hnorm : ‖w₁ - w₂‖ ≤ Real.sqrt 3 * (b - a) := by rw [← dist_eq_norm]; exact hdist
  -- Separation contradiction.
  have hsep := sepPrec_separates' p hp0 hp w₁ w₂ hr₁ hr₂ hne
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3nn : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hpow : (0 : ℝ) < 2 ^ (-(Hex.sepPrec p : ℤ)) := by positivity
  have hchain : 4 * 2 ^ (-(Hex.sepPrec p : ℤ)) < Real.sqrt 3 * (b - a) := by
    linarith [hsep, hnorm]
  have hwidth : Real.sqrt 3 * (b - a) ≤ Real.sqrt 3 * 2 ^ (-(Hex.sepPrec p : ℤ)) :=
    mul_le_mul_of_nonneg_left hw h3nn
  have hlt4 : 4 * 2 ^ (-(Hex.sepPrec p : ℤ)) < Real.sqrt 3 * 2 ^ (-(Hex.sepPrec p : ℤ)) :=
    lt_of_lt_of_le hchain hwidth
  have h4 : (4 : ℝ) < Real.sqrt 3 := lt_of_mul_lt_mul_right hlt4 hpow.le
  nlinarith [h4, h3, h3nn]

/-- **The `V = 1 ∧ p(hi) = 0` row is impossible at the depth budget.** It puts
two real roots — an interior root and `hi` — in `(lo, hi]`, a Sturm count of `2`,
contradicting `sturmCount_le_one`. -/
theorem bisect_refute_double (hdeg : 1 ≤ (p.degree?).getD 0)
    (hp : Hex.ZPoly.SquareFreeRat p) {lo hi : Dyadic} (hlt : lo < hi)
    (hw : Dyadic.toReal hi - Dyadic.toReal lo ≤ (2 : ℝ) ^ (-(Hex.sepPrec p : ℤ)))
    (hV1 : Hex.descartesVar (Hex.mobiusTransform p ⟨lo, hi, hlt⟩) = 1)
    (hbz : (Hex.dyadicSign (p.evalDyadic hi) == 0) = true) :
    False := by
  have hp0 : p ≠ 0 := by
    intro hh; rw [hh] at hdeg; simp only [Hex.DensePoly.degree?_zero_getD] at hdeg; omega
  have hP0 : toPolyℝ p ≠ 0 := fun h => hp0 (toPolyℝ_eq_zero_iff.mp h)
  have hab : Dyadic.toReal lo < Dyadic.toReal hi := toReal_lt_toReal_iff.mpr hlt
  set M := mobiusPoly ((p.degree?).getD 0) (Dyadic.toReal lo) (Dyadic.toReal hi) (toPolyℝ p) with hM
  have hMne : M ≠ 0 := mobiusPoly_ne_zero_of_ne (ne_of_lt hab) hP0
  have hV : Hex.descartesVar (Hex.mobiusTransform p ⟨lo, hi, hlt⟩) = Polynomial.signVariations M :=
    descartesVar_mobiusTransform p ⟨lo, hi, hlt⟩ hdeg
  have hSV1 : Polynomial.signVariations M = 1 := by rw [← hV]; exact hV1
  have hcp := Polynomial.countP_pos_eq_one_of_signVariations_eq_one hMne hSV1
  have hroot : (toPolyℝ p).IsRoot (Dyadic.toReal hi) := (bZero_iff hi).mp hbz
  have hcnt := descartes_node_count hdeg hp hlt
  rw [← hM] at hcnt
  have h2 : (Hex.sturmVarAt (Hex.ZPoly.sturmChain p) lo : Int)
      - Hex.sturmVarAt (Hex.ZPoly.sturmChain p) hi = 2 := by
    rw [hcnt, hcp, if_pos hroot]; norm_num
  have hle := sturmCount_le_one hdeg hp ⟨lo, hi, hlt⟩ hw
  have hle' : (Hex.sturmVarAt (Hex.ZPoly.sturmChain p) lo : Int)
      - Hex.sturmVarAt (Hex.ZPoly.sturmChain p) hi ≤ 1 := hle
  omega

/-! ### The Descartes worklist drains -/

/-- **The `descartesVisit` worklist drains, ordered and count-exact.** For a
positive-degree square-free `p`, on a nonempty interval whose width is within the
depth budget, `descartesVisit` returns `some arr` where `arr` is an ordered array
of `arr.size = sturmVarAt chain lo − sturmVarAt chain hi` isolations, each with
its interval inside `(lo, hi]`.

Structural induction on `depth`. Candidate and discard nodes are exact leaves
(`node_candidate`, `node_discard`, no budget). The bisecting rows are refuted at
`depth = 0` (`bisect_refute_double`, `bisect_refute_sector`) and recurse into
halved children at `depth + 1`; the size telescopes and the emissions stay
ordered exactly as in `sturmVisit_spec`. -/
private theorem descartesVisit_spec (hdeg : 1 ≤ (p.degree?).getD 0)
    (hp : Hex.ZPoly.SquareFreeRat p) :
    ∀ (depth : Nat) (lo hi : Dyadic),
      lo < hi →
      Dyadic.toReal hi - Dyadic.toReal lo ≤ (2 : ℝ) ^ ((depth : ℤ) - (Hex.sepPrec p : ℤ)) →
      ∃ arr : Array (Hex.RealRootIsolation p),
        Hex.descartesVisit p (Hex.ZPoly.sturmChain p) rfl depth lo hi = some arr ∧
        arr.size = Hex.sturmVarAt (Hex.ZPoly.sturmChain p) lo
          - Hex.sturmVarAt (Hex.ZPoly.sturmChain p) hi ∧
        (∀ i j : Fin arr.size, i < j → arr[i].interval.upper ≤ arr[j].interval.lower) ∧
        (∀ I ∈ arr, lo ≤ I.interval.lower) ∧ (∀ I ∈ arr, I.interval.upper ≤ hi) := by
  intro depth
  induction depth with
  | zero =>
    intro lo hi hlt hw
    simp only [Nat.cast_zero, zero_sub] at hw
    have hunf : Hex.descartesVisit p (Hex.ZPoly.sturmChain p) rfl 0 lo hi
        = (if hlt' : lo < hi then
            (if dispatchC p lo hi hlt' then
              (if h : (Hex.sturmVarAt (Hex.ZPoly.sturmChain p) lo : Int)
                  - Hex.sturmVarAt (Hex.ZPoly.sturmChain p) hi = 1 then
                some #[⟨⟨lo, hi, hlt'⟩, by exact h⟩]
              else none)
            else if Hex.descartesVar (Hex.mobiusTransform p ⟨lo, hi, hlt'⟩) = 0 then
              some #[]
            else none)
          else some #[]) := rfl
    rw [dif_pos hlt] at hunf
    by_cases hC : dispatchC p lo hi hlt = true
    · -- candidate leaf
      have hcert := node_candidate hdeg hp hlt hC
      rw [if_pos hC, dif_pos hcert] at hunf
      refine ⟨#[⟨⟨lo, hi, hlt⟩, by exact hcert⟩], hunf, ?_, ?_, ?_, ?_⟩
      · simp only [Array.size_singleton]; omega
      · intro i j hij
        have hi1 : (i : ℕ) < 1 := i.isLt
        have hj1 : (j : ℕ) < 1 := j.isLt
        have hij' : (i : ℕ) < (j : ℕ) := hij
        omega
      · intro I hI
        simp only [List.mem_toArray, List.mem_singleton] at hI
        subst hI; exact dle_refl lo
      · intro I hI
        simp only [List.mem_toArray, List.mem_singleton] at hI
        subst hI; exact dle_refl hi
    · -- either discard leaf or a refuted bisect
      rw [if_neg hC] at hunf
      have hCfalse : dispatchC p lo hi hlt = false := by
        cases h : dispatchC p lo hi hlt with
        | false => rfl
        | true => exact absurd h hC
      by_cases hV0 : Hex.descartesVar (Hex.mobiusTransform p ⟨lo, hi, hlt⟩) = 0
      · -- discard leaf
        have hcert := node_discard hdeg hp hlt hCfalse hV0
        rw [if_pos hV0] at hunf
        refine ⟨#[], hunf, ?_, ?_, ?_, ?_⟩
        · simp only [Array.size_empty]; omega
        · intro i j hij; exact absurd i.isLt (by simp)
        · intro I hI; simp at hI
        · intro I hI; simp at hI
      · -- bisect at depth 0: refuted
        exfalso
        rw [if_neg hV0] at hunf
        rcases Nat.lt_or_ge (Hex.descartesVar (Hex.mobiusTransform p ⟨lo, hi, hlt⟩)) 2 with hV2 | hV2
        · have hV1 : Hex.descartesVar (Hex.mobiusTransform p ⟨lo, hi, hlt⟩) = 1 := by omega
          have hbz : (Hex.dyadicSign (p.evalDyadic hi) == 0) = true := by
            unfold dispatchC at hCfalse; rw [hV1] at hCfalse; simpa using hCfalse
          exact bisect_refute_double hdeg hp hlt hw hV1 hbz
        · exact bisect_refute_sector hdeg hp hlt hw hV2
  | succ d ih =>
    intro lo hi hlt hw
    have hunf : Hex.descartesVisit p (Hex.ZPoly.sturmChain p) rfl (d + 1) lo hi
        = (if hlt' : lo < hi then
            (if dispatchC p lo hi hlt' then
              (if h : (Hex.sturmVarAt (Hex.ZPoly.sturmChain p) lo : Int)
                  - Hex.sturmVarAt (Hex.ZPoly.sturmChain p) hi = 1 then
                some #[⟨⟨lo, hi, hlt'⟩, by exact h⟩]
              else none)
            else if Hex.descartesVar (Hex.mobiusTransform p ⟨lo, hi, hlt'⟩) = 0 then
              some #[]
            else
              match Hex.descartesVisit p (Hex.ZPoly.sturmChain p) rfl d lo
                  ((lo + hi) >>> (1 : Int)) with
              | none => none
              | some left =>
                match Hex.descartesVisit p (Hex.ZPoly.sturmChain p) rfl d
                    ((lo + hi) >>> (1 : Int)) hi with
                | none => none
                | some right => some (left ++ right))
          else some #[]) := rfl
    rw [dif_pos hlt] at hunf
    by_cases hC : dispatchC p lo hi hlt = true
    · have hcert := node_candidate hdeg hp hlt hC
      rw [if_pos hC, dif_pos hcert] at hunf
      refine ⟨#[⟨⟨lo, hi, hlt⟩, by exact hcert⟩], hunf, ?_, ?_, ?_, ?_⟩
      · simp only [Array.size_singleton]; omega
      · intro i j hij
        have hi1 : (i : ℕ) < 1 := i.isLt
        have hj1 : (j : ℕ) < 1 := j.isLt
        have hij' : (i : ℕ) < (j : ℕ) := hij
        omega
      · intro I hI
        simp only [List.mem_toArray, List.mem_singleton] at hI
        subst hI; exact dle_refl lo
      · intro I hI
        simp only [List.mem_toArray, List.mem_singleton] at hI
        subst hI; exact dle_refl hi
    · rw [if_neg hC] at hunf
      have hCfalse : dispatchC p lo hi hlt = false := by
        cases h : dispatchC p lo hi hlt with
        | false => rfl
        | true => exact absurd h hC
      by_cases hV0 : Hex.descartesVar (Hex.mobiusTransform p ⟨lo, hi, hlt⟩) = 0
      · have hcert := node_discard hdeg hp hlt hCfalse hV0
        rw [if_pos hV0] at hunf
        refine ⟨#[], hunf, ?_, ?_, ?_, ?_⟩
        · simp only [Array.size_empty]; omega
        · intro i j hij; exact absurd i.isLt (by simp)
        · intro I hI; simp at hI
        · intro I hI; simp at hI
      · -- bisect: recurse into the two halves
        rw [if_neg hV0] at hunf
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
            ≤ (2 : ℝ) ^ ((d : ℤ) - (Hex.sepPrec p : ℤ)) := by rw [hmidR]; linarith
        have hwr : Dyadic.toReal hi - Dyadic.toReal ((lo + hi) >>> (1 : Int))
            ≤ (2 : ℝ) ^ ((d : ℤ) - (Hex.sepPrec p : ℤ)) := by rw [hmidR]; linarith
        obtain ⟨left, hLeq, hLsize, hLord, hLlo, hLhi⟩ := ih lo ((lo + hi) >>> (1 : Int)) hlm hwl
        obtain ⟨right, hReq, hRsize, hRord, hRlo, hRhi⟩ := ih ((lo + hi) >>> (1 : Int)) hi hmh hwr
        have hle1 : Hex.sturmVarAt (Hex.ZPoly.sturmChain p) ((lo + hi) >>> (1 : Int))
            ≤ Hex.sturmVarAt (Hex.ZPoly.sturmChain p) lo := sturmVarAt_le hdeg hp hlm
        have hle2 : Hex.sturmVarAt (Hex.ZPoly.sturmChain p) hi
            ≤ Hex.sturmVarAt (Hex.ZPoly.sturmChain p) ((lo + hi) >>> (1 : Int)) :=
          sturmVarAt_le hdeg hp hmh
        refine ⟨left ++ right, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hunf, hLeq, hReq]
        · rw [Array.size_append, hLsize, hRsize]; omega
        · intro i j hij
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

/-! ### Driver completeness -/

/-- The positive-degree core: the worklist drains (`descartesVisit_spec`) and the
emitted total matches `rootCount p = sturmVarNegInf − sturmVarPosInf` (the
`±rootBound` gap counts every root), so `assemble?` certifies. -/
private theorem isolateDescartes?_isSome_of_degree_pos (hdeg : 1 ≤ (p.degree?).getD 0)
    (hp : Hex.ZPoly.SquareFreeRat p) : (Hex.isolateDescartes? p).isSome := by
  obtain ⟨d, hd⟩ : ∃ d, p.degree? = some (d + 1) := by
    rcases hh : p.degree? with _ | n
    · rw [hh] at hdeg; simp at hdeg
    · rcases n with _ | m
      · rw [hh] at hdeg; simp at hdeg
      · exact ⟨m, rfl⟩
  have hlt : -(Hex.rootBound p) < Hex.rootBound p := neg_rootBound_lt_rootBound p
  obtain ⟨arr, hvisit, hsize, hord, -, -⟩ :=
    descartesVisit_spec hdeg hp (Hex.isolationDepth p) (-(Hex.rootBound p)) (Hex.rootBound p)
      hlt (initial_width_le p hdeg)
  have hInt := sturmVar_neg_pos_sub hdeg hp
  have hsize' : arr.size = Hex.sturmVarNegInf (Hex.ZPoly.sturmChain p)
      - Hex.sturmVarPosInf (Hex.ZPoly.sturmChain p) := by
    have hrc : Hex.rootCount p = Hex.sturmVarNegInf (Hex.ZPoly.sturmChain p)
        - Hex.sturmVarPosInf (Hex.ZPoly.sturmChain p) := rfl
    rw [hsize, ← hrc]; omega
  -- `isolateDescartes?` on positive-degree square-free `p` is the top run + `assemble?`.
  have heq : Hex.isolateDescartes? p
      = (match Hex.descartesVisit p (Hex.ZPoly.sturmChain p) rfl (Hex.isolationDepth p)
            (-(Hex.rootBound p)) (Hex.rootBound p) with
          | none => none
          | some arr => Hex.assemble? p (Hex.ZPoly.sturmChain p) rfl arr) := by
    unfold Hex.isolateDescartes?
    simp only [hd]
    rw [if_pos hp]
    rfl
  rw [heq, hvisit]
  exact assemble?_isSome rfl arr hord hsize'

/-- The Descartes engine on a nonzero constant: the driver's `some 0` branch
hands `assemble?` the empty array through the empty chain. -/
private theorem isolateDescartes?_isSome_of_degree_zero (hd : p.degree? = some 0) :
    (Hex.isolateDescartes? p).isSome := by
  have heq : Hex.isolateDescartes? p = Hex.assemble? p (Hex.ZPoly.sturmChain p) rfl #[] := by
    unfold Hex.isolateDescartes?; rw [hd]
  have hchain0 : Hex.ZPoly.sturmChain p = #[] := by
    unfold Hex.ZPoly.sturmChain; rw [hd]; rfl
  rw [heq]
  refine assemble?_isSome rfl #[] ?_ ?_
  · intro i j hij; exact absurd i.isLt (by simp)
  · rw [hchain0]; rfl

/-- **The Descartes engine succeeds on nonzero square-free input.** The last
theorem of `HexRealRootsMathlib`: `isolateDescartes? p ≠ none` for nonzero `p`
passing the executable `SquareFreeRat` test, so the runtime never falls back to
the Sturm engine.

Positive degree is the real content (`isolateDescartes?_isSome_of_degree_pos`,
the two-circle termination argument); a nonzero constant certifies through the
empty chain. As with `isolateSturm?_isSome`, the `p ≠ 0` hypothesis is added
because `SquareFreeRat 0` is vacuous while `isolateDescartes? 0 = none`. -/
theorem isolateDescartes?_isSome (p : Hex.ZPoly) (hp0 : p ≠ 0)
    (hp : Hex.ZPoly.SquareFreeRat p) : (Hex.isolateDescartes? p).isSome := by
  rcases hd : p.degree? with _ | n
  · exact absurd hd (degree?_ne_none hp0)
  · rcases n with _ | n
    · exact isolateDescartes?_isSome_of_degree_zero hd
    · exact isolateDescartes?_isSome_of_degree_pos (by simp [hd]) hp

end

end HexRealRootsMathlib
