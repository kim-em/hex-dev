/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexArith.Nat.Prime
public meta import HexBerlekamp.Factor
public meta import HexBerlekamp.Irreducibility
public meta import HexHensel.Basic
public meta import HexHensel.Multifactor
public meta import HexHensel.QuadraticMultifactor
public meta import HexMatrix.Basic
public meta import HexPolyZ.Mignotte
public meta import HexLLL.Basic
public import HexArith.Nat.Prime
public import HexBerlekamp.Factor
public import HexBerlekamp.Irreducibility
public import HexHensel.Multifactor
public import HexHensel.QuadraticMultifactor
public import HexLLL.Basic
-- Needed so `decide`/`rfl` over `DensePoly`/`Array` equality reduces in the
-- kernel: the core `Array.instDecidableEq` delegates its nonempty case to the
-- non-`@[expose]` `Array.instDecidableEqImpl`, which is otherwise opaque under
-- the module system. Drop once that impl is exposed upstream (lean4).
import all Init.Data.Array.DecidableEq

public import HexBerlekampZassenhaus.Lattice
public meta import HexBerlekampZassenhaus.Lattice
import all HexBerlekampZassenhaus.PrimeSelection
import all HexBerlekampZassenhaus.Records
import all HexBerlekampZassenhaus.Certificate
import all HexBerlekampZassenhaus.ChoosePrimeData
import all HexBerlekampZassenhaus.ReassemblyProofs
import all HexBerlekampZassenhaus.Lattice

public section
set_option backward.proofsInPublic true
set_option backward.privateInPublic true

/-!
This module collects `bhksIndicatorCandidates?`, the dilate lemmas, and candidate-correctness proofs.
-/
namespace Hex

private def cldGuardG : ZPoly :=
  DensePoly.ofCoeffs #[-2, 1]

#guard cldQuotientMod cldGuardF cldGuardG 5 2 = DensePoly.ofCoeffs #[22, 1]
#guard (cldCoeffs cldGuardF 5 2 cldGuardG).size = cldGuardF.degree?.getD 0

/-
Regression guard for #6217. The exact integer CLD coefficient of
`cldGuardF = x^2 - 5x + 6` against the true factor `g = x - 2` at index 0 is
`-3`, so under the centered cut the executable `cldCoeffs` at this index is
`0`. Without ambient centering the result was `125`, which exceeded
`bhksCoeffBound cldGuardF 0 = 16`.
-/
#guard (cldCoeffs cldGuardF 5 6 cldGuardG).getD 0 0 = 0
#guard (cldCoeffs cldGuardF 5 6 cldGuardG).getD 1 0 = 0

/-
Regression guard for #7817.  At `p = 5`, `a = 4`, `b = 1`, the aggregate
residue `311 + 311` wraps to `-3` before the lower cut, so the aggregate cut is
small even though the sum of separately cut residues is large.
-/
#guard psiCut 5 4 1 (311 + 311) = -1
#guard psiCut 5 4 1 311 + psiCut 5 4 1 311 = 124
#guard psiCut 5 4 1 (311 + 311) ≠ psiCut 5 4 1 311 + psiCut 5 4 1 311

namespace BHKS

/--
BHKS Lemma 5.1 column bound for the executable `cldCoeffs`.

If there exists an exact integer `y` (morally `[x^j] (f * g'.derivative / g')`
for a true integer factor `g'` of `f` that Hensel-lifts to `g`) congruent to
`(cldQuotientMod f g p a).coeff j` modulo `p^a` and satisfying
`|y| ≤ bhksCoeffBound f j`, then under the Hensel precision hypothesis
`2 * bhksCoeffBound f j < p^a` and `p ≥ 2`, the executable `cldCoeffs` entry
at index `j` is bounded by `bhksCoeffBound f j`.

This replaces the original unconditional `#5224` target — the
counterexample of `#6217` showed the executable cut had to be re-centered at
the ambient modulus before this column bound could hold. The recentering
landed in `Hex.psiCut`; the bound is then a direct consequence of
`abs_psiCut_le_of_natAbs_le` plus `precisionForCoeffBound_spec` for the
lower cut threshold.
-/
theorem abs_cldCoeffs_le_bhksCoeffBound
    (f g : ZPoly) (p a j : Nat) (y : Int)
    (hp : 2 ≤ p)
    (hbound : y.natAbs ≤ bhksCoeffBound f j)
    (hsep_a : 2 * bhksCoeffBound f j < p ^ a)
    (hcongr : y % ((p ^ a : Nat) : Int) =
              (cldQuotientMod f g p a).coeff j % ((p ^ a : Nat) : Int)) :
    ((cldCoeffs f p a g).getD j 0).natAbs ≤ bhksCoeffBound f j := by
  have hsep_b : 2 * bhksCoeffBound f j < p ^ bhksCoeffCutThreshold p f j := by
    unfold bhksCoeffCutThreshold
    have := le_pow_ceilLogP hp (2 * bhksCoeffBound f j + 1)
    omega
  by_cases hlt : j < f.degree?.getD 0
  · rw [cldCoeffs_getD_of_lt f p a g j hlt]
    exact abs_psiCut_le_of_natAbs_le p a (bhksCoeffCutThreshold p f j)
      y ((cldQuotientMod f g p a).coeff j) (bhksCoeffBound f j)
      hbound hsep_a hsep_b hcongr
  · -- Out-of-range index: `cldCoeffs` returns 0 by `Array.getD` default.
    have hsize :
        (cldCoeffs f p a g).size = f.degree?.getD 0 := by
      unfold cldCoeffs
      simp
    have hge : (cldCoeffs f p a g).size ≤ j := by
      simpa [hsize] using Nat.le_of_not_lt hlt
    rw [Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none hge]
    simp

end BHKS

private def bhksGuardFactors : Array ZPoly :=
  #[DensePoly.ofCoeffs #[-2, 1], DensePoly.ofCoeffs #[-3, 1]]

private def bhksGuardBasis : BhksLatticeBasis :=
  bhksLatticeBasis cldGuardF 5 2 bhksGuardFactors

#guard bhksGuardBasis.factorCount = 2
#guard bhksGuardBasis.coeffWidth = 2
#guard bhksGuardBasis.basis[(0, 0)] = 1
#guard bhksGuardBasis.basis[(0, 1)] = 0
#guard bhksGuardBasis.basis[(0, 2)] = (bhksGuardBasis.cldRows.getD 0 #[]).getD 0 0
#guard bhksGuardBasis.basis[(0, 3)] = (bhksGuardBasis.cldRows.getD 0 #[]).getD 1 0
#guard bhksGuardBasis.basis[(0, 2)] ≠ bhksGuardFactors[0].coeff 0
#guard bhksGuardBasis.basis[(1, 0)] = 0
#guard bhksGuardBasis.basis[(1, 1)] = 1
#guard bhksGuardBasis.basis[(2, 0)] = 0
#guard bhksGuardBasis.basis[(2, 2)] =
  Int.ofNat (5 ^ (2 - bhksGuardBasis.cutThresholds.getD 0 0))
#guard bhksGuardBasis.basis[(3, 3)] =
  Int.ofNat (5 ^ (2 - bhksGuardBasis.cutThresholds.getD 1 0))
#guard bhksCutRadiusSq4 bhksGuardBasis = 16
#guard bhksProjectIndicator 2 2 (bhksGuardBasis.basis.getRow ⟨0, by decide⟩) = #[1, 0]
#guard (bhksProjectIndicator 2 2 (bhksGuardBasis.basis.getRow ⟨0, by decide⟩)).size = bhksGuardBasis.factorCount

/--
Lift the projected integer rows of `L` into a rational row-basis matrix
sized `n × r`, with `n := L.projectedRows.size` and `r := L.factorCount`.
The matrix is the input to BHKS Lemma 3.3 RREF-based equivalence-class
identification.
-/
@[expose]
def bhksProjectedRowsAsRatMatrix
    (rows : Array (Array Int)) (n r : Nat) : Matrix Rat n r :=
  Matrix.ofFn fun i j =>
    ((rows.getD i.val #[]).getD j.val (0 : Int) : Rat)

private def bhksColumnSignature
    (echelonRows : Array (Array Rat)) (j : Nat) : Array Rat :=
  echelonRows.map (·.getD j 0)

@[expose]
def bhksInsertSignatureClass
    (sig : Array Rat) (j : Nat) :
    List (Array Rat × List Nat) → List (Array Rat × List Nat)
  | [] => [(sig, [j])]
  | (s, members) :: rest =>
      if s = sig then (s, members ++ [j]) :: rest
      else (s, members) :: bhksInsertSignatureClass sig j rest

private def bhksClassIndicator (r : Nat) (members : List Nat) : Array Int :=
  ((List.range r).map (fun i => if i ∈ members then (1 : Int) else 0)).toArray

/--
BHKS equivalence-class indicator vectors over the projected lattice rows
of `L`.

Lifts the projected integer rows into a rational row-basis matrix, runs
`Matrix.rowReduce` over `Q`, and groups column indices `0, …, r - 1` by their
echelon-column signature: indices `i` and `j` are equivalent iff every
echelon row agrees at positions `i` and `j` (BHKS Lemma 3.3 / FLINT
Algorithm 8). Each equivalence class produces one compact `0/1` indicator
of length `r`. Classes are emitted in the order they are first observed by
ascending column index.
-/
@[expose]
def bhksEquivalenceClassIndicators (L : BhksProjectedRows) : Array (Array Int) :=
  let n := L.projectedRows.size
  let r := L.factorCount
  let M : Matrix Rat n r := bhksProjectedRowsAsRatMatrix L.projectedRows n r
  let D := Matrix.rowReduce M
  let echelonRows : Array (Array Rat) := D.echelon.rows.toArray.map (·.toArray)
  let groups : List (List Nat) :=
    ((List.range r).foldl
        (fun acc j =>
          bhksInsertSignatureClass (bhksColumnSignature echelonRows j) j acc)
        []).map Prod.snd
  (groups.map (fun cls => bhksClassIndicator r cls)).toArray

private def bhksTwoClassProjectedRows : BhksProjectedRows :=
  { factorCount := 4
    coeffWidth := 0
    cutRadiusSq4 := 0
    reducedRowCount := 1
    projectedRows := #[#[1, 1, 0, 0]] }

#guard bhksEquivalenceClassIndicators bhksTwoClassProjectedRows =
  #[#[1, 1, 0, 0], #[0, 0, 1, 1]]

private def bhksSingletonClassProjectedRows : BhksProjectedRows :=
  { factorCount := 3
    coeffWidth := 0
    cutRadiusSq4 := 0
    reducedRowCount := 0
    projectedRows := #[] }

#guard bhksEquivalenceClassIndicators bhksSingletonClassProjectedRows =
  #[#[1, 1, 1]]

private def bhksNoProgressProjectedRows : BhksProjectedRows :=
  { factorCount := 3
    coeffWidth := 0
    cutRadiusSq4 := 0
    reducedRowCount := 3
    projectedRows := #[#[1, 0, 0], #[0, 1, 0], #[0, 0, 1]] }

#guard bhksEquivalenceClassIndicators bhksNoProgressProjectedRows =
  #[#[1, 0, 0], #[0, 1, 0], #[0, 0, 1]]

@[expose]
def liftModulus (d : LiftData) : Nat :=
  d.p ^ d.k

@[expose]
def centeredLiftPoly (f : ZPoly) (m : Nat) : ZPoly :=
  DensePoly.ofCoeffs <| f.toArray.map fun coeff => centeredModNat coeff m

/-- Coefficientwise description of `centeredLiftPoly`. -/
theorem coeff_centeredLiftPoly (f : ZPoly) (m i : Nat) :
    (centeredLiftPoly f m).coeff i = centeredModNat (f.coeff i) m := by
  have hzero : centeredModNat (0 : Int) m = 0 := centeredModNat_zero m
  unfold centeredLiftPoly
  rw [DensePoly.coeff_ofCoeffs]
  unfold DensePoly.toArray DensePoly.coeff Array.getD
  by_cases hi : i < f.coeffs.size
  · simp [hi, Array.getElem_map]
  · simp [hi]
    change (0 : Int) = centeredModNat 0 m
    exact hzero.symm

theorem centeredLiftPoly_reduceModPow_eq_of_coeff_natAbs_le
    (g : ZPoly) (p k B : Nat)
    (hbound : ∀ i, (g.coeff i).natAbs ≤ B)
    (hsep : 2 * B < p ^ k) :
    centeredLiftPoly (ZPoly.reduceModPow g p k) (p ^ k) = g := by
  apply DensePoly.ext_coeff
  intro i
  rw [coeff_centeredLiftPoly]
  have hpk : 0 < p ^ k := by omega
  rw [ZPoly.coeff_reduceModPow_eq_emod_of_pos _ _ _ _ hpk]
  exact centeredModNat_emod_eq_of_natAbs_le (g.coeff i) (p ^ k) B (hbound i) hsep

theorem centeredLiftPoly_eq_of_reduceModPow_eq
    (g h : ZPoly) (p k B : Nat)
    (hbound : ∀ i, (g.coeff i).natAbs ≤ B)
    (hsep : 2 * B < p ^ k)
    (hreduce : ZPoly.reduceModPow h p k = ZPoly.reduceModPow g p k) :
    centeredLiftPoly (ZPoly.reduceModPow h p k) (p ^ k) = g := by
  rw [hreduce]
  exact centeredLiftPoly_reduceModPow_eq_of_coeff_natAbs_le g p k B hbound hsep

/-- Normalize a candidate integer factor by extracting its primitive part and
flipping sign so the leading coefficient is non-negative.  Used by
`bhksIndicatorCandidate?` to produce a canonical witness from the centred
lift of a scaled lifted-factor product. -/
@[expose]
def normalizeCandidateFactor (candidate : ZPoly) : ZPoly :=
  let primitive := ZPoly.primitivePart candidate
  if DensePoly.leadingCoeff primitive < 0 then
    DensePoly.scale (-1 : Int) primitive
  else
    primitive

/--
`normalizeCandidateFactor g = g` when `g` is already primitive (content `1`)
and has non-negative leading coefficient.  This is the A2 reconstruction step
that asserts the canonical witness produced by `bhksIndicatorCandidate?`
agrees with the expected true factor under those normalization assumptions.
-/
theorem normalizeCandidateFactor_eq_of_primitive_nonneg_leading
    (g : ZPoly) (hprim : ZPoly.Primitive g)
    (hsign : 0 ≤ DensePoly.leadingCoeff g) :
    normalizeCandidateFactor g = g := by
  unfold normalizeCandidateFactor
  have hpart : ZPoly.primitivePart g = g :=
    ZPoly.primitivePart_eq_self_of_primitive g hprim
  rw [hpart]
  have hnot_neg : ¬ DensePoly.leadingCoeff g < 0 := Int.not_lt.mpr hsign
  rw [if_neg hnot_neg]

def bhksIndicatorSelectedFactors
    (liftedFactors : Array ZPoly) (indicator : Array Int) : Option (Array ZPoly) :=
  if indicator.size != liftedFactors.size then
    none
  else
    let indices := List.range indicator.size
    if indices.all (fun i => indicator.getD i 0 == 0 || indicator.getD i 0 == 1) &&
        indices.any (fun i => indicator.getD i 0 == 1) then
      some <| indices.foldl
        (fun selected i =>
          if indicator.getD i 0 == 1 then
            selected.push (liftedFactors.getD i 0)
          else
            selected)
        #[]
    else
      none

/-- The array selected by a `0/1` BHKS indicator row. -/
def bhksIndicatorSelectedFactorsArray
    (liftedFactors : Array ZPoly) (indicator : Array Int) : Array ZPoly :=
  (List.range indicator.size).foldl
    (fun selected i =>
      if indicator.getD i 0 == 1 then
        selected.push (liftedFactors.getD i 0)
      else
        selected)
    #[]

/--
Successful branch of `bhksIndicatorSelectedFactors` for well-formed `0/1`
indicator rows, returning the canonical selected-factor array.
-/
theorem bhksIndicatorSelectedFactors_eq_some_selectedArray_of_getD
    (liftedFactors : Array ZPoly) (indicator : Array Int)
    (hsize : indicator.size = liftedFactors.size)
    (hbits : ∀ i, i < indicator.size →
      indicator.getD i 0 = 0 ∨ indicator.getD i 0 = 1)
    (hnonempty : ∃ i, i < indicator.size ∧ indicator.getD i 0 = 1) :
    bhksIndicatorSelectedFactors liftedFactors indicator =
      some (bhksIndicatorSelectedFactorsArray liftedFactors indicator) := by
  unfold bhksIndicatorSelectedFactors bhksIndicatorSelectedFactorsArray
  have hsizeBool : (indicator.size != liftedFactors.size) = false := by
    simp [hsize]
  rw [hsizeBool]
  simp only [Bool.false_eq_true, if_false]
  have hall :
      (List.range indicator.size).all
          (fun i => indicator.getD i 0 == 0 || indicator.getD i 0 == 1) = true := by
    rw [List.all_eq_true]
    intro i hi
    have hi_size : i < indicator.size := List.mem_range.mp hi
    rcases hbits i hi_size with hzero | hone
    · simp [hzero]
    · simp [hone]
  have hany :
      (List.range indicator.size).any
          (fun i => indicator.getD i 0 == 1) = true := by
    rw [List.any_eq_true]
    rcases hnonempty with ⟨i, hi_size, hone⟩
    exact ⟨i, List.mem_range.mpr hi_size, by simp [hone]⟩
  change
    (if
        ((List.range indicator.size).all
            (fun i => indicator.getD i 0 == 0 || indicator.getD i 0 == 1) &&
          (List.range indicator.size).any
            (fun i => indicator.getD i 0 == 1)) = true then
      some
        ((List.range indicator.size).foldl
          (fun selected i =>
            if (indicator.getD i 0 == 1) = true then
              selected.push (liftedFactors.getD i 0)
            else
              selected)
          #[])
    else
      none) =
      some
        ((List.range indicator.size).foldl
          (fun selected i =>
            if (indicator.getD i 0 == 1) = true then
              selected.push (liftedFactors.getD i 0)
            else
              selected)
          #[])
  rw [hall, hany]
  rfl

/--
Successful branch of `bhksIndicatorSelectedFactors`, stated with an explicit
name for the selected-factor array chosen by the caller.
-/
theorem bhksIndicatorSelectedFactors_eq_some_of_getD
    (liftedFactors : Array ZPoly) (indicator : Array Int)
    (selected : Array ZPoly)
    (hsize : indicator.size = liftedFactors.size)
    (hbits : ∀ i, i < indicator.size →
      indicator.getD i 0 = 0 ∨ indicator.getD i 0 = 1)
    (hnonempty : ∃ i, i < indicator.size ∧ indicator.getD i 0 = 1)
    (hselected :
      selected = bhksIndicatorSelectedFactorsArray liftedFactors indicator) :
    bhksIndicatorSelectedFactors liftedFactors indicator = some selected := by
  rw [hselected]
  exact
    bhksIndicatorSelectedFactors_eq_some_selectedArray_of_getD
      liftedFactors indicator hsize hbits hnonempty

/--
Reconstruct and verify one BHKS equivalence-class indicator.

The indicator row is supplied by the later RREF recovery stage. This helper
only checks that the row is a nonempty `0/1` vector over the lifted factors,
forms the selected lifted-factor product, applies the centred integer lift,
dilates back from the monic-transform coordinate, normalizes content and sign,
and accepts the candidate only when exact division of `f` succeeds.
-/
def bhksIndicatorCandidate?
    (f : ZPoly) (d : LiftData) (indicator : Array Int) : Option (ZPoly × ZPoly) :=
  match bhksIndicatorSelectedFactors d.liftedFactors indicator with
  | none => none
  | some selected =>
      let modulus := liftModulus d
      let candidate := normalizeFactorSign <| normalizeCandidateFactor <|
        ZPoly.dilate (DensePoly.leadingCoeff f) <|
          centeredLiftPoly (Array.polyProduct selected) modulus
      if shouldRecordPolynomialFactor candidate then
        match exactQuotient? f candidate with
        | some quotient => some (candidate, quotient)
        | none => none
      else
        none

set_option maxHeartbeats 800000
private theorem bhksIndicatorCandidate?_normalizeFactorSign
    {f : ZPoly} {d : LiftData} {indicator : Array Int}
    {candidate quotient : ZPoly}
    (h : bhksIndicatorCandidate? f d indicator = some (candidate, quotient)) :
    normalizeFactorSign candidate = candidate := by
  unfold bhksIndicatorCandidate? at h
  cases hselected : bhksIndicatorSelectedFactors d.liftedFactors indicator with
  | none =>
      simp [hselected] at h
  | some selected =>
      simp only [hselected] at h
      let modulus := liftModulus d
      let candidate0 :=
        normalizeCandidateFactor
          (ZPoly.dilate (DensePoly.leadingCoeff f)
            (centeredLiftPoly (Array.polyProduct selected) modulus))
      let candidate' := normalizeFactorSign candidate0
      change
        (if shouldRecordPolynomialFactor candidate' then
          match exactQuotient? f candidate' with
          | some quotient => some (candidate', quotient)
          | none => none
        else
          none) = some (candidate, quotient) at h
      by_cases hrecord : shouldRecordPolynomialFactor candidate'
      · rw [if_pos hrecord] at h
        cases hquot : exactQuotient? f candidate' with
        | none =>
            simp [hquot] at h
        | some quotient' =>
            simp [hquot] at h
            rcases h with ⟨hcandidate, _hquotient⟩
            subst candidate
            exact normalizeFactorSign_idem candidate0
      · rw [if_neg hrecord] at h
        simp at h

private theorem bhksIndicatorCandidate?_shouldRecord
    {f : ZPoly} {d : LiftData} {indicator : Array Int}
    {candidate quotient : ZPoly}
    (h : bhksIndicatorCandidate? f d indicator = some (candidate, quotient)) :
    shouldRecordPolynomialFactor candidate = true := by
  unfold bhksIndicatorCandidate? at h
  cases hselected : bhksIndicatorSelectedFactors d.liftedFactors indicator with
  | none =>
      simp [hselected] at h
  | some selected =>
      simp only [hselected] at h
      let modulus := liftModulus d
      let candidate0 :=
        normalizeCandidateFactor
          (ZPoly.dilate (DensePoly.leadingCoeff f)
            (centeredLiftPoly (Array.polyProduct selected) modulus))
      let candidate' := normalizeFactorSign candidate0
      change
        (if shouldRecordPolynomialFactor candidate' then
          match exactQuotient? f candidate' with
          | some quotient => some (candidate', quotient)
          | none => none
        else
          none) = some (candidate, quotient) at h
      by_cases hrecord : shouldRecordPolynomialFactor candidate'
      · rw [if_pos hrecord] at h
        cases hquot : exactQuotient? f candidate' with
        | none =>
            simp [hquot] at h
        | some quotient' =>
            simp [hquot] at h
            rcases h with ⟨hcandidate, _hquotient⟩
            subst candidate
            exact hrecord
      · rw [if_neg hrecord] at h
        simp at h

/--
A successful BHKS indicator candidate divides `f`. The executable
`bhksIndicatorCandidate?` only returns `some (candidate, _)` after
`exactQuotient? f candidate` succeeds, so the candidate is a verified
integer divisor of `f`.
-/
theorem bhksIndicatorCandidate?_dvd
    {f : ZPoly} {d : LiftData} {indicator : Array Int}
    {candidate quotient : ZPoly}
    (h : bhksIndicatorCandidate? f d indicator = some (candidate, quotient)) :
    candidate ∣ f := by
  unfold bhksIndicatorCandidate? at h
  cases hselected : bhksIndicatorSelectedFactors d.liftedFactors indicator with
  | none =>
      simp [hselected] at h
  | some selected =>
      simp only [hselected] at h
      let modulus := liftModulus d
      let candidate0 :=
        normalizeCandidateFactor
          (ZPoly.dilate (DensePoly.leadingCoeff f)
            (centeredLiftPoly (Array.polyProduct selected) modulus))
      let candidate' := normalizeFactorSign candidate0
      change
        (if shouldRecordPolynomialFactor candidate' then
          match exactQuotient? f candidate' with
          | some quotient => some (candidate', quotient)
          | none => none
        else
          none) = some (candidate, quotient) at h
      by_cases hrecord : shouldRecordPolynomialFactor candidate'
      · rw [if_pos hrecord] at h
        cases hquot : exactQuotient? f candidate' with
        | none =>
            simp [hquot] at h
        | some quotient' =>
            simp [hquot] at h
            rcases h with ⟨hcandidate, hquotient⟩
            subst candidate
            subst quotient
            have hmul : quotient' * candidate' = f := exactQuotient?_product hquot
            refine ⟨quotient', ?_⟩
            rw [DensePoly.mul_comm_poly (S := Int)]
            exact hmul.symm
      · rw [if_neg hrecord] at h
        simp at h

/-- If `normalizeCandidateFactor g` is nonzero, it is primitive: the inner
`primitivePart g` must then be nonzero, hence `content g ≠ 0`, hence
`content (primitivePart g) = 1` (and `scale (-1)` preserves content). -/
private theorem normalizeCandidateFactor_primitive
    {g : ZPoly} (hne : normalizeCandidateFactor g ≠ 0) :
    ZPoly.Primitive (normalizeCandidateFactor g) := by
  unfold normalizeCandidateFactor at hne ⊢
  by_cases hlead :
      DensePoly.leadingCoeff (ZPoly.primitivePart g) < 0
  · rw [if_pos hlead] at hne ⊢
    have hprim_ne :
        (ZPoly.primitivePart g : ZPoly) ≠ 0 := by
      intro hzero
      apply hne
      show DensePoly.scale (-1 : Int) (ZPoly.primitivePart g) = 0
      rw [hzero]
      exact DensePoly.scale_neg_one_zero
    have hcontent_ne : ZPoly.content g ≠ 0 := by
      intro hzero
      apply hprim_ne
      show DensePoly.primitivePart g = 0
      exact
        DensePoly.primitivePart_eq_zero_of_content_eq_zero g
          (by simpa [ZPoly.content] using hzero)
    have hprim_primitive : ZPoly.Primitive (ZPoly.primitivePart g) :=
      ZPoly.primitivePart_primitive g hcontent_ne
    show ZPoly.content
        (DensePoly.scale (-1 : Int) (ZPoly.primitivePart g)) = 1
    rw [show ZPoly.content
            (DensePoly.scale (-1 : Int) (ZPoly.primitivePart g))
          = DensePoly.content
              (DensePoly.scale (-1 : Int) (ZPoly.primitivePart g)) from rfl,
        DensePoly.content_scale_neg_one (ZPoly.primitivePart g)]
    exact hprim_primitive
  · rw [if_neg hlead] at hne ⊢
    have hcontent_ne : ZPoly.content g ≠ 0 := by
      intro hzero
      apply hne
      show DensePoly.primitivePart g = 0
      exact
        DensePoly.primitivePart_eq_zero_of_content_eq_zero g
          (by simpa [ZPoly.content] using hzero)
    exact ZPoly.primitivePart_primitive g hcontent_ne

/-- A successful BHKS indicator candidate has nonnegative leading coefficient:
the final `normalizeFactorSign` layer is a fixed point on the candidate, so
the candidate inherits the `≥ 0` leading-coefficient guarantee of
`normalizeFactorSign`. -/
private theorem bhksIndicatorCandidate?_leadingCoeff_nonneg
    {f : ZPoly} {d : LiftData} {indicator : Array Int}
    {candidate quotient : ZPoly}
    (h : bhksIndicatorCandidate? f d indicator = some (candidate, quotient)) :
    0 ≤ DensePoly.leadingCoeff candidate := by
  have hnorm := bhksIndicatorCandidate?_normalizeFactorSign h
  have hsign := normalizeFactorSign_leadingCoeff_nonneg candidate
  rwa [hnorm] at hsign

/-- A successful BHKS indicator candidate is primitive: the candidate equals
`normalizeFactorSign (normalizeCandidateFactor _)`, and `shouldRecord = true`
forces the inner factor to be nonzero, hence primitive. -/
theorem bhksIndicatorCandidate?_primitive
    {f : ZPoly} {d : LiftData} {indicator : Array Int}
    {candidate quotient : ZPoly}
    (h : bhksIndicatorCandidate? f d indicator = some (candidate, quotient)) :
    ZPoly.Primitive candidate := by
  unfold bhksIndicatorCandidate? at h
  cases hselected : bhksIndicatorSelectedFactors d.liftedFactors indicator with
  | none =>
      simp [hselected] at h
  | some selected =>
      simp only [hselected] at h
      let modulus := liftModulus d
      let candidate0 :=
        normalizeCandidateFactor
          (ZPoly.dilate (DensePoly.leadingCoeff f)
            (centeredLiftPoly (Array.polyProduct selected) modulus))
      let candidate' := normalizeFactorSign candidate0
      change
        (if shouldRecordPolynomialFactor candidate' then
          match exactQuotient? f candidate' with
          | some quotient => some (candidate', quotient)
          | none => none
        else
          none) = some (candidate, quotient) at h
      by_cases hrecord : shouldRecordPolynomialFactor candidate'
      · rw [if_pos hrecord] at h
        cases hquot : exactQuotient? f candidate' with
        | none =>
            simp [hquot] at h
        | some quotient' =>
            simp [hquot] at h
            rcases h with ⟨hcandidate, _hquotient⟩
            subst candidate
            have hcand'_ne : candidate' ≠ 0 := by
              intro hzero
              rw [hzero] at hrecord
              unfold shouldRecordPolynomialFactor at hrecord
              simp at hrecord
            have hcand0_ne : candidate0 ≠ 0 := by
              intro hzero
              apply hcand'_ne
              show normalizeFactorSign candidate0 = 0
              rw [hzero]
              unfold normalizeFactorSign
              have hlc :
                  ¬ DensePoly.leadingCoeff (0 : ZPoly) < 0 := by
                simp
              rw [if_neg hlc]
            have hprim_cand0 : ZPoly.Primitive candidate0 :=
              normalizeCandidateFactor_primitive hcand0_ne
            exact normalizeFactorSign_primitive _ hprim_cand0
      · rw [if_neg hrecord] at h
        simp at h

/-- A successful BHKS indicator candidate has positive degree: it is primitive
with nonnegative leading coefficient and is not a unit, so it cannot be a
constant polynomial. -/
private theorem bhksIndicatorCandidate?_positive_degree
    {f : ZPoly} {d : LiftData} {indicator : Array Int}
    {candidate quotient : ZPoly}
    (h : bhksIndicatorCandidate? f d indicator = some (candidate, quotient)) :
    0 < candidate.degree?.getD 0 := by
  have hrecord := bhksIndicatorCandidate?_shouldRecord h
  have hprim := bhksIndicatorCandidate?_primitive h
  have hsign := bhksIndicatorCandidate?_leadingCoeff_nonneg h
  have hne : candidate ≠ 0 := by
    intro hzero
    rw [hzero] at hrecord
    unfold shouldRecordPolynomialFactor at hrecord
    simp at hrecord
  have hne_one : candidate ≠ 1 := by
    intro hone
    rw [hone] at hrecord
    unfold shouldRecordPolynomialFactor at hrecord
    simp at hrecord
  have hne_neg : candidate ≠ DensePoly.C (-1 : Int) := by
    intro hneg
    rw [hneg] at hrecord
    unfold shouldRecordPolynomialFactor at hrecord
    simp at hrecord
  -- Show `candidate.size ≥ 2`.  Otherwise `candidate` collapses to a
  -- constant polynomial, and `Primitive` + `0 ≤ leadingCoeff` + `≠ 0` + `≠ 1`
  -- + `≠ DensePoly.C (-1)` gives a contradiction.
  have hsize_pos : 0 < candidate.size := by
    rcases Nat.lt_or_ge 0 candidate.size with hpos | _hle
    · exact hpos
    · have hsz : candidate.size = 0 := by omega
      have hcand_zero : candidate = 0 := by
        apply DensePoly.ext_coeff
        intro n
        rw [DensePoly.coeff_zero]
        exact DensePoly.coeff_eq_zero_of_size_le candidate (by omega)
      exact False.elim (hne hcand_zero)
  have hsize_ge_two : 2 ≤ candidate.size := by
    rcases Nat.lt_or_ge 1 candidate.size with hge | _hle
    · omega
    · have hsize_one : candidate.size = 1 := by omega
      have hcandidate_eq : candidate = DensePoly.C (candidate.coeff 0) := by
        apply DensePoly.ext_coeff
        intro n
        cases n with
        | zero =>
            rw [DensePoly.coeff_C]
            simp
        | succ n =>
            rw [DensePoly.coeff_C, if_neg (Nat.succ_ne_zero n)]
            exact DensePoly.coeff_eq_zero_of_size_le candidate (by omega)
      have hprim_C :
          DensePoly.content (DensePoly.C (candidate.coeff 0)) = 1 := by
        have hcontent_eq : DensePoly.content candidate
            = DensePoly.content (DensePoly.C (candidate.coeff 0)) :=
          congrArg DensePoly.content hcandidate_eq
        exact hcontent_eq.symm.trans hprim
      have hcontent_C_eq :
          DensePoly.content (DensePoly.C (candidate.coeff 0))
            = Int.ofNat (candidate.coeff 0).natAbs :=
        DensePoly.content_C (candidate.coeff 0)
      have hnat_int :
          Int.ofNat (candidate.coeff 0).natAbs = 1 := by
        rw [← hcontent_C_eq]
        exact hprim_C
      have hnat : (candidate.coeff 0).natAbs = 1 := by
        exact Int.ofNat.inj hnat_int
      have hc_cases :
          candidate.coeff 0 = ↑(1 : Nat) ∨ candidate.coeff 0 = -↑(1 : Nat) :=
        Int.natAbs_eq_iff.mp hnat
      exfalso
      rcases hc_cases with hpos | hneg
      · apply hne_one
        rw [hcandidate_eq]
        show DensePoly.C (candidate.coeff 0) = DensePoly.C 1
        rw [hpos]
        rfl
      · apply hne_neg
        rw [hcandidate_eq]
        show DensePoly.C (candidate.coeff 0) = DensePoly.C (-1)
        rw [hneg]
        rfl
  -- Now `candidate.size ≥ 2`, so degree = size - 1 ≥ 1 > 0.
  have hne_size : candidate.size ≠ 0 := by omega
  have hdeg_eq :
      (DensePoly.degree? candidate).getD 0 = candidate.size - 1 := by
    unfold DensePoly.degree?
    rw [dif_neg hne_size]
    rfl
  show 0 < (DensePoly.degree? candidate).getD 0
  rw [hdeg_eq]
  omega

/--
The candidate returned by a successful `bhksIndicatorCandidate?` call is
exactly the canonical normalization of the centred lift after dilation from the
monic-transform coordinate. This is a Mathlib-free surface lemma that
downstream Mathlib-side proofs use to identify the candidate against the
dilated centred lift, avoiding the need to reference the private `liftModulus`
definition from outside this file.
-/
theorem bhksIndicatorCandidate?_eq_normalized_dilatedCenteredLift
    {f : ZPoly} {d : LiftData} {indicator : Array Int}
    {candidate quotient : ZPoly} {selected : Array ZPoly}
    (h : bhksIndicatorCandidate? f d indicator = some (candidate, quotient))
    (hselected : bhksIndicatorSelectedFactors d.liftedFactors indicator = some selected) :
    candidate = normalizeFactorSign (normalizeCandidateFactor
      (ZPoly.dilate (DensePoly.leadingCoeff f)
        (centeredLiftPoly (Array.polyProduct selected) (d.p ^ d.k)))) := by
  unfold bhksIndicatorCandidate? at h
  rw [hselected] at h
  let modulus := liftModulus d
  let candidate0 :=
    normalizeCandidateFactor
      (ZPoly.dilate (DensePoly.leadingCoeff f)
        (centeredLiftPoly (Array.polyProduct selected) modulus))
  let candidate' := normalizeFactorSign candidate0
  change
    (if shouldRecordPolynomialFactor candidate' then
      match exactQuotient? f candidate' with
      | some quotient => some (candidate', quotient)
      | none => none
    else
      none) = some (candidate, quotient) at h
  by_cases hrecord : shouldRecordPolynomialFactor candidate'
  · rw [if_pos hrecord] at h
    cases hquot : exactQuotient? f candidate' with
    | none => simp [hquot] at h
    | some quotient' =>
        simp [hquot] at h
        rcases h with ⟨hcandidate, _hquotient⟩
        subst candidate
        simp [candidate', candidate0, modulus, liftModulus]
  · rw [if_neg hrecord] at h
    simp at h

/--
A2 reconstruction surface for a single BHKS indicator, stated at the
Mathlib-free executable layer. If the indicator selects `selected`, the
dilation of the selected product's centred lift is the expected factor, the
expected factor is already canonical under primitive/sign normalization, and it
divides `f` as a positive-leading-coefficient positive-degree factor, then
`bhksIndicatorCandidate?` returns that expected factor with some quotient.
-/
theorem bhksIndicatorCandidate?_eq_some_of_dilatedCenteredLift
    (f : ZPoly) (d : LiftData) (indicator : Array Int)
    (selected : Array ZPoly) (expectedFactor : ZPoly)
    (hselected :
      bhksIndicatorSelectedFactors d.liftedFactors indicator = some selected)
    (hdvd : expectedFactor ∣ f)
    (hexpected_prim : ZPoly.Primitive expectedFactor)
    (hexpected_sign : 0 ≤ DensePoly.leadingCoeff expectedFactor)
    (hexpected_pos_lc : 0 < DensePoly.leadingCoeff expectedFactor)
    (hexpected_degree : 0 < expectedFactor.degree?.getD 0)
    (hdilated :
      ZPoly.dilate (DensePoly.leadingCoeff f)
          (centeredLiftPoly (Array.polyProduct selected) (d.p ^ d.k)) =
        expectedFactor) :
    ∃ quotient,
      bhksIndicatorCandidate? f d indicator = some (expectedFactor, quotient) := by
  have hnormalizeCandidate :
      normalizeCandidateFactor
          (ZPoly.dilate (DensePoly.leadingCoeff f)
            (centeredLiftPoly (Array.polyProduct selected) (d.p ^ d.k))) =
        expectedFactor := by
    rw [hdilated]
    exact normalizeCandidateFactor_eq_of_primitive_nonneg_leading
      expectedFactor hexpected_prim hexpected_sign
  have hnormalize :
      normalizeFactorSign (normalizeCandidateFactor
          (ZPoly.dilate (DensePoly.leadingCoeff f)
            (centeredLiftPoly (Array.polyProduct selected) (d.p ^ d.k)))) =
        expectedFactor := by
    rw [hnormalizeCandidate]
    exact normalizeFactorSign_eq_self_of_leadingCoeff_nonneg expectedFactor hexpected_sign
  have hrecord :
      shouldRecordPolynomialFactor expectedFactor = true := by
    apply shouldRecordPolynomialFactor_eq_true_of_ne
    · intro hzero
      rw [hzero] at hexpected_degree
      simp [DensePoly.degree?] at hexpected_degree
    · intro hone
      rw [hone] at hexpected_degree
      have hdeg0 : (DensePoly.degree? (1 : ZPoly)).getD 0 = 0 := by
        rfl
      rw [hdeg0] at hexpected_degree
      omega
    · intro hneg
      rw [hneg] at hexpected_degree
      have hdeg0 : (DensePoly.degree? (DensePoly.C (-1 : Int))).getD 0 = 0 := by
        simp
      rw [hdeg0] at hexpected_degree
      omega
  rcases hdvd with ⟨quotient, hquotient_mul⟩
  have hmul : quotient * expectedFactor = f := by
    rw [DensePoly.mul_comm_poly (S := Int)]
    exact hquotient_mul.symm
  have hquotient :
      exactQuotient? f expectedFactor = some quotient :=
    exactQuotient?_eq_some_of_pos_lc_pos_degree_mul_eq
      hexpected_pos_lc hexpected_degree hmul
  refine ⟨quotient, ?_⟩
  unfold bhksIndicatorCandidate?
  rw [hselected]
  change
    (let modulus := liftModulus d
     let candidate :=
       normalizeFactorSign <| normalizeCandidateFactor
         (ZPoly.dilate (DensePoly.leadingCoeff f)
           (centeredLiftPoly (Array.polyProduct selected) modulus))
     if shouldRecordPolynomialFactor candidate then
       match exactQuotient? f candidate with
       | some quotient => some (candidate, quotient)
       | none => none
     else
       none) = some (expectedFactor, quotient)
  simp [liftModulus, hnormalize, hrecord, hquotient]

def bhksIndicatorOneCount (r : Nat) (indicator : Array Int) : Nat :=
  (List.range r).foldl
    (fun count i => if indicator.getD i 0 == 1 then count + 1 else count)
    0

def bhksIndicatorAllOnes (r : Nat) (indicator : Array Int) : Bool :=
  indicator.size == r && bhksIndicatorOneCount r indicator == r

/-- The recovery early-bailout predicate: the projected lattice is empty, the
indicator partition is empty, or the indicator partition is the trivial
all-ones single class. -/
def bhksDegenerateIndicatorPartition
    (L : BhksProjectedRows) (indicators : Array (Array Int)) : Bool :=
  indicators.isEmpty ||
    L.projectedRows.isEmpty ||
    (indicators.size == 1 &&
      bhksIndicatorAllOnes L.factorCount (indicators.getD 0 #[]))

private def bhksIndicatorCandidatesStep
    (f : ZPoly) (d : LiftData) :
    Option (Array ZPoly) → Array Int → Option (Array ZPoly)
  | none, _ => none
  | some candidates, indicator =>
      match bhksIndicatorCandidate? f d indicator with
      | some candidate => some (candidates.push candidate.1)
      | none => none

/-- Reconstruct and verify every BHKS equivalence-class indicator candidate.

Folds `bhksIndicatorCandidate?` over the list of indicator vectors, pushing the
verified candidate factor onto the accumulator on success and short-circuiting
to `none` on the first reconstruction failure. -/
def bhksIndicatorCandidates?
    (f : ZPoly) (d : LiftData) (indicators : Array (Array Int)) :
    Option (Array ZPoly) :=
  indicators.foldl (bhksIndicatorCandidatesStep f d) (some #[])

private theorem bhksIndicatorCandidatesStep_fold_none
    (f : ZPoly) (d : LiftData) (indicators : List (Array Int)) :
    List.foldl (bhksIndicatorCandidatesStep f d) none indicators = none := by
  induction indicators with
  | nil => rfl
  | cons indicator indicators ih =>
      rw [List.foldl_cons]
      simpa [bhksIndicatorCandidatesStep] using ih

private theorem bhksIndicatorCandidatesStep_fold_all_of_candidate
    (P : ZPoly → Prop)
    (f : ZPoly) (d : LiftData)
    (hcandidate :
      ∀ {indicator candidate quotient},
        bhksIndicatorCandidate? f d indicator = some (candidate, quotient) →
          P candidate) :
    ∀ (indicators : List (Array Int)) (acc candidates : Array ZPoly),
      (∀ factor ∈ acc.toList, P factor) →
        List.foldl (bhksIndicatorCandidatesStep f d) (some acc) indicators =
            some candidates →
          ∀ factor ∈ candidates.toList, P factor
  | [], acc, candidates, hacc, hfold => by
      simp at hfold
      cases hfold
      exact hacc
  | indicator :: indicators, acc, candidates, hacc, hfold => by
      rw [List.foldl_cons] at hfold
      cases hhead : bhksIndicatorCandidate? f d indicator with
      | none =>
          have hnone :=
            bhksIndicatorCandidatesStep_fold_none f d indicators
          simp [bhksIndicatorCandidatesStep, hhead, hnone] at hfold
      | some pair =>
          rcases pair with ⟨candidate, quotient⟩
          have hnext :
              List.foldl (bhksIndicatorCandidatesStep f d) (some (acc.push candidate))
                  indicators = some candidates := by
            simpa [bhksIndicatorCandidatesStep, hhead] using hfold
          have hacc_push :
              ∀ factor ∈ (acc.push candidate).toList, P factor := by
            intro factor hmem
            rw [Array.toList_push] at hmem
            simp only [List.mem_append, List.mem_singleton] at hmem
            cases hmem with
            | inl hacc_mem => exact hacc factor hacc_mem
            | inr hfactor =>
                rw [hfactor]
                exact hcandidate hhead
          exact
            bhksIndicatorCandidatesStep_fold_all_of_candidate
              P f d hcandidate indicators (acc.push candidate) candidates
              hacc_push hnext

private theorem bhksIndicatorCandidates?_all_of_candidate
    (P : ZPoly → Prop)
    (f : ZPoly) (d : LiftData)
    (hcandidate :
      ∀ {indicator candidate quotient},
        bhksIndicatorCandidate? f d indicator = some (candidate, quotient) →
          P candidate)
    {indicators : Array (Array Int)} {candidates : Array ZPoly}
    (h : bhksIndicatorCandidates? f d indicators = some candidates) :
    ∀ factor ∈ candidates.toList, P factor := by
  unfold bhksIndicatorCandidates? at h
  rw [← Array.foldl_toList] at h
  exact
    bhksIndicatorCandidatesStep_fold_all_of_candidate
      P f d hcandidate indicators.toList #[] candidates (by simp) h

private theorem bhksIndicatorCandidates?_normalizeFactorSign
    {f : ZPoly} {d : LiftData} {indicators : Array (Array Int)}
    {candidates : Array ZPoly}
    (h : bhksIndicatorCandidates? f d indicators = some candidates) :
    ∀ factor ∈ candidates.toList, normalizeFactorSign factor = factor :=
  bhksIndicatorCandidates?_all_of_candidate
    (fun factor => normalizeFactorSign factor = factor)
    f d (fun hcandidate => bhksIndicatorCandidate?_normalizeFactorSign hcandidate) h

private theorem bhksIndicatorCandidates?_shouldRecord
    {f : ZPoly} {d : LiftData} {indicators : Array (Array Int)}
    {candidates : Array ZPoly}
    (h : bhksIndicatorCandidates? f d indicators = some candidates) :
    ∀ factor ∈ candidates.toList, shouldRecordPolynomialFactor factor = true :=
  bhksIndicatorCandidates?_all_of_candidate
    (fun factor => shouldRecordPolynomialFactor factor = true)
    f d (fun hcandidate => bhksIndicatorCandidate?_shouldRecord hcandidate) h

/-- Every candidate emitted by `bhksIndicatorCandidates?` divides the
input polynomial; this is the per-candidate version of the verified
exact-division check performed inside `bhksIndicatorCandidate?`. -/
theorem bhksIndicatorCandidates?_dvd
    {f : ZPoly} {d : LiftData} {indicators : Array (Array Int)}
    {candidates : Array ZPoly}
    (h : bhksIndicatorCandidates? f d indicators = some candidates) :
    ∀ factor ∈ candidates.toList, factor ∣ f :=
  bhksIndicatorCandidates?_all_of_candidate
    (fun factor => factor ∣ f)
    f d (fun hcandidate => bhksIndicatorCandidate?_dvd hcandidate) h

/-- Every candidate emitted by `bhksIndicatorCandidates?` is primitive.  This
is the array-level form of the per-candidate primitivity guarantee from
`normalizeCandidateFactor` plus sign normalisation. -/
theorem bhksIndicatorCandidates?_primitive
    {f : ZPoly} {d : LiftData} {indicators : Array (Array Int)}
    {candidates : Array ZPoly}
    (h : bhksIndicatorCandidates? f d indicators = some candidates) :
    ∀ factor ∈ candidates.toList, ZPoly.Primitive factor :=
  bhksIndicatorCandidates?_all_of_candidate
    (fun factor => ZPoly.Primitive factor)
    f d (fun hcandidate => bhksIndicatorCandidate?_primitive hcandidate) h

/-- Every candidate emitted by `bhksIndicatorCandidates?` has nonnegative
leading coefficient; this is the array-level form of the per-candidate sign
normalisation guarantee. -/
theorem bhksIndicatorCandidates?_leadingCoeff_nonneg
    {f : ZPoly} {d : LiftData} {indicators : Array (Array Int)}
    {candidates : Array ZPoly}
    (h : bhksIndicatorCandidates? f d indicators = some candidates) :
    ∀ factor ∈ candidates.toList, 0 ≤ DensePoly.leadingCoeff factor :=
  bhksIndicatorCandidates?_all_of_candidate
    (fun factor => 0 ≤ DensePoly.leadingCoeff factor)
    f d (fun hcandidate => bhksIndicatorCandidate?_leadingCoeff_nonneg hcandidate) h

/-- Every candidate emitted by `bhksIndicatorCandidates?` has positive degree;
this is the array-level form of the per-candidate nonconstant guarantee. -/
theorem bhksIndicatorCandidates?_positive_degree
    {f : ZPoly} {d : LiftData} {indicators : Array (Array Int)}
    {candidates : Array ZPoly}
    (h : bhksIndicatorCandidates? f d indicators = some candidates) :
    ∀ factor ∈ candidates.toList, 0 < factor.degree?.getD 0 :=
  bhksIndicatorCandidates?_all_of_candidate
    (fun factor => 0 < factor.degree?.getD 0)
    f d (fun hcandidate => bhksIndicatorCandidate?_positive_degree hcandidate) h

private theorem array_toList_getD {α : Type}
    (xs : Array α) (i : Nat) (fallback : α) :
    xs.toList.getD i fallback = xs.getD i fallback := by
  cases xs with
  | mk data =>
      rw [List.getD_eq_getElem?_getD]
      unfold Array.getD Array.size Array.getInternal
      by_cases hlt : i < data.length
      · rw [dif_pos hlt]
        simp [List.getElem?_eq_getElem hlt]
      · rw [dif_neg hlt]
        simp [List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt hlt)]

private theorem bhksIndicatorCandidatesStep_fold_eq_some
    (f : ZPoly) (d : LiftData)
    (pref : List ZPoly) (indicators : List (Array Int)) (candidates quotients : List ZPoly)
    (hsize : candidates.length = indicators.length)
    (hcandidate :
      ∀ i, i < indicators.length →
        bhksIndicatorCandidate? f d (indicators.getD i #[]) =
          some (candidates.getD i 0, quotients.getD i 0)) :
    indicators.foldl (bhksIndicatorCandidatesStep f d) (some pref.toArray) =
      some ((pref ++ candidates).toArray) := by
  induction indicators generalizing pref candidates quotients with
  | nil =>
      cases candidates with
      | nil => simp
      | cons candidate candidates => simp at hsize
  | cons indicator indicators ih =>
      cases candidates with
      | nil => simp at hsize
      | cons candidate candidates =>
          have hhead :
              bhksIndicatorCandidate? f d indicator =
                some (candidate, quotients.getD 0 0) := by
            simpa using hcandidate 0 (by simp)
          have htail_size : candidates.length = indicators.length := by
            simpa using hsize
          have htail :
              ∀ i, i < indicators.length →
                bhksIndicatorCandidate? f d (indicators.getD i #[]) =
                  some (candidates.getD i 0, (quotients.drop 1).getD i 0) := by
            intro i hi
            have h := hcandidate (i + 1) (by simp [hi])
            simpa [List.getD_cons_succ] using h
          rw [List.foldl_cons]
          simp [bhksIndicatorCandidatesStep, hhead]
          simpa [List.append_assoc] using
            ih (pref := pref ++ [candidate]) (candidates := candidates)
              (quotients := quotients.drop 1) htail_size htail

/--
If each BHKS equivalence-class indicator reconstructs and verifies to the
corresponding candidate factor, the executable candidate fold returns the
whole candidate array.

The `quotients` array records the exact-division witnesses returned by
`bhksIndicatorCandidate?`; only the first component is accumulated by
`bhksIndicatorCandidates?`.
-/
theorem bhksIndicatorCandidates?_eq_some_of_forall_candidate
    (f : ZPoly) (d : LiftData)
    (indicators : Array (Array Int)) (candidates quotients : Array ZPoly)
    (hsize : candidates.size = indicators.size)
    (hcandidate :
      ∀ i, i < indicators.size →
        bhksIndicatorCandidate? f d (indicators.getD i #[]) =
          some (candidates.getD i 0, quotients.getD i 0)) :
    bhksIndicatorCandidates? f d indicators = some candidates := by
  unfold bhksIndicatorCandidates?
  rw [← Array.foldl_toList]
  have hlist :
      indicators.toList.foldl (bhksIndicatorCandidatesStep f d) (some #[]) =
        some ([].append candidates.toList).toArray := by
    apply bhksIndicatorCandidatesStep_fold_eq_some
      (quotients := quotients.toList)
    · simpa using hsize
    · intro i hi
      have h := hcandidate i (by simpa using hi)
      have hindicator :
          indicators.toList.getD i #[] = indicators.getD i #[] := by
        exact array_toList_getD indicators i #[]
      have hcand :
          candidates.toList.getD i 0 = candidates.getD i 0 := by
        exact array_toList_getD candidates i 0
      have hquot :
          quotients.toList.getD i 0 = quotients.getD i 0 := by
        exact array_toList_getD quotients i 0
      simpa [hindicator, hcand, hquot] using h
  simpa using hlist

private theorem bhksIndicatorCandidates?_foldl_eq_some_append
    (f : ZPoly) (d : LiftData) :
    ∀ (indicators : List (Array Int)) (candidates : List ZPoly) (acc : Array ZPoly),
      (hlength : candidates.length = indicators.length) →
      (∀ i (hi : i < indicators.length),
        ∃ quotient,
          bhksIndicatorCandidate? f d indicators[i] =
            some (candidates[i]'(by rw [hlength]; exact hi), quotient)) →
      List.foldl (bhksIndicatorCandidatesStep f d) (some acc) indicators =
        some (acc ++ candidates.toArray)
  | [], candidates, acc, hlength, _ => by
      have hcandidates : candidates = [] := List.eq_nil_of_length_eq_zero hlength
      subst hcandidates
      apply congrArg some
      rw [← Array.toList_inj]
      simp
  | indicator :: indicators, candidates, acc, hlength, hcandidate => by
      cases candidates with
      | nil => simp at hlength
      | cons candidate candidates =>
          have hhead :
              ∃ quotient,
                bhksIndicatorCandidate? f d indicator = some (candidate, quotient) := by
            simpa using hcandidate 0 (Nat.succ_pos _)
          rcases hhead with ⟨quotient, hhead⟩
          have hlength_tail : candidates.length = indicators.length := by
            simpa using Nat.succ.inj hlength
          have htail :
              ∀ i (hi : i < indicators.length),
                ∃ quotient,
                  bhksIndicatorCandidate? f d indicators[i] =
                    some (candidates[i]'(by rw [hlength_tail]; exact hi), quotient) := by
            intro i hi
            simpa using hcandidate (i + 1) (Nat.succ_lt_succ hi)
          calc
            List.foldl (bhksIndicatorCandidatesStep f d) (some acc)
                (indicator :: indicators)
                =
              List.foldl (bhksIndicatorCandidatesStep f d)
                (some (acc.push candidate)) indicators := by
                  simp [bhksIndicatorCandidatesStep, hhead]
            _ = some (acc.push candidate ++ candidates.toArray) := by
                  exact bhksIndicatorCandidates?_foldl_eq_some_append
                    f d indicators candidates (acc.push candidate) hlength_tail htail
            _ = some (acc ++ (candidate :: candidates).toArray) := by
                  apply congrArg some
                  rw [← Array.toList_inj]
                  simp [Array.toList_append]

/--
Assemble the BHKS candidate fold from per-indicator reconstruction facts.

This is the proof-facing surface for callers that know every indicator row
reconstructs and exactly divides `f`: with a size agreement and one quotient
witness for each row, the executable fold returns the requested candidate
array.
-/
theorem bhksIndicatorCandidates?_eq_some_of_getD
    (f : ZPoly) (d : LiftData)
    (indicators : Array (Array Int)) (candidates : Array ZPoly)
    (hsize : candidates.size = indicators.size)
    (hcandidate :
      ∀ i, i < indicators.size →
        ∃ quotient,
          bhksIndicatorCandidate? f d (indicators.getD i #[]) =
            some (candidates.getD i 0, quotient)) :
    bhksIndicatorCandidates? f d indicators = some candidates := by
  unfold bhksIndicatorCandidates?
  rw [← Array.foldl_toList]
  have hlength : candidates.toList.length = indicators.toList.length := by
    simpa [Array.length_toList] using hsize
  have hcandidate_list :
      ∀ i (hi : i < indicators.toList.length),
        ∃ quotient,
          bhksIndicatorCandidate? f d indicators.toList[i] =
            some (candidates.toList[i]'(by rw [hlength]; exact hi), quotient) := by
    intro i hi
    have hi_array : i < indicators.size := by
      simpa [Array.length_toList] using hi
    have hi_candidates : i < candidates.size := by
      simpa [hsize] using hi_array
    rcases hcandidate i hi_array with ⟨quotient, hquotient⟩
    refine ⟨quotient, ?_⟩
    have hind :
        indicators.toList[i] = indicators.getD i #[] := by
      simp [Array.getD, Array.getElem_toList, hi_array]
    have hcand :
        candidates.toList[i] = candidates.getD i 0 := by
      simp [Array.getD, Array.getElem_toList, hi_candidates]
    rw [hind, hcand]
    exact hquotient
  have hfold :=
    bhksIndicatorCandidates?_foldl_eq_some_append f d
      indicators.toList candidates.toList #[] hlength hcandidate_list
  rw [hfold]
  apply congrArg some
  rw [← Array.toList_inj]
  simp

private theorem bhksIndicatorCandidatesStep_fold_size_eq
    (f : ZPoly) (d : LiftData) :
    ∀ (indicators : List (Array Int)) (acc candidates : Array ZPoly),
      List.foldl (bhksIndicatorCandidatesStep f d) (some acc) indicators =
          some candidates →
        candidates.size = acc.size + indicators.length
  | [], acc, candidates, hfold => by
      simp at hfold
      cases hfold
      simp
  | indicator :: indicators, acc, candidates, hfold => by
      rw [List.foldl_cons] at hfold
      cases hhead : bhksIndicatorCandidate? f d indicator with
      | none =>
          have hnone :=
            bhksIndicatorCandidatesStep_fold_none f d indicators
          simp [bhksIndicatorCandidatesStep, hhead, hnone] at hfold
      | some pair =>
          rcases pair with ⟨candidate, quotient⟩
          have hnext :
              List.foldl (bhksIndicatorCandidatesStep f d)
                  (some (acc.push candidate)) indicators = some candidates := by
            simpa [bhksIndicatorCandidatesStep, hhead] using hfold
          have ih :=
            bhksIndicatorCandidatesStep_fold_size_eq f d indicators
              (acc.push candidate) candidates hnext
          rw [ih, Array.size_push, List.length_cons]
          omega

/--
A successful BHKS indicator-candidate fold produces a candidate array of the
same size as the input indicator array.  This is the size identity used by
`ExpectedTrueFactors`-shaped consumers that need to align the per-index
indicator and factor views.
-/
theorem bhksIndicatorCandidates?_size_eq
    {f : ZPoly} {d : LiftData} {indicators : Array (Array Int)}
    {candidates : Array ZPoly}
    (h : bhksIndicatorCandidates? f d indicators = some candidates) :
    candidates.size = indicators.size := by
  unfold bhksIndicatorCandidates? at h
  rw [← Array.foldl_toList] at h
  have hfold :=
    bhksIndicatorCandidatesStep_fold_size_eq f d indicators.toList #[] candidates h
  simpa [Array.length_toList] using hfold

private theorem array_getD_push_lt {α : Type}
    (xs : Array α) (a fallback : α) {i : Nat} (hi : i < xs.size) :
    (xs.push a).getD i fallback = xs.getD i fallback := by
  have hi_list : i < xs.toList.length := by
    simpa [Array.length_toList] using hi
  rw [← array_toList_getD (xs.push a) i fallback,
    ← array_toList_getD xs i fallback, Array.toList_push,
    List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left hi_list]

private theorem array_getD_push_size {α : Type}
    (xs : Array α) (a fallback : α) :
    (xs.push a).getD xs.size fallback = a := by
  rw [← array_toList_getD (xs.push a) xs.size fallback,
    Array.toList_push, List.getD_eq_getElem?_getD]
  have hsize : xs.size = xs.toList.length := by
    simp [Array.length_toList]
  rw [hsize]
  simp

/-- Powers of an integer add their exponents. The executable layer is
Mathlib-free, so the generic `pow_add` is unavailable; this small induction
stands in for it. -/
private theorem int_pow_add (a : Int) (m k : Nat) :
    a ^ (m + k) = a ^ m * a ^ k := by
  induction k with
  | zero => rw [Nat.add_zero, Lean.Grind.Semiring.pow_zero, Int.mul_one]
  | succ k ih =>
      rw [Nat.add_succ, Lean.Grind.Semiring.pow_succ, ih,
        Lean.Grind.Semiring.pow_succ, Int.mul_assoc]

namespace ZPoly.ToMonicData

/-- General coefficient law for the monic transform `transformedCore`. Below the
top degree the coefficient is `core.coeff n` scaled by a power of the leading
coefficient; the top coefficient is `1`; higher coefficients vanish. -/
theorem transformedCore_coeff (core : ZPoly) (degree n : Nat) :
    (transformedCore core degree).coeff n =
      if n < degree then
        core.coeff n * DensePoly.leadingCoeff core ^ (degree - 1 - n)
      else if n = degree then 1 else 0 := by
  rcases Nat.lt_trichotomy n degree with h | h | h
  · rw [if_pos h]
    change (transformedCoeffs core degree).getD n (0 : Int) = _
    unfold transformedCoeffs
    rw [array_getD_push_lt ((List.range degree).map
          (fun i => core.coeff i * DensePoly.leadingCoeff core ^ (degree - 1 - i))).toArray
        1 0 (by simpa using h)]
    rw [← array_toList_getD, List.toList_toArray, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_range h]
    simp
  · subst h
    rw [if_neg (Nat.lt_irrefl _), if_pos rfl]
    exact transformedCore_coeff_top core n
  · rw [if_neg (by omega), if_neg (by omega)]
    exact DensePoly.coeff_eq_zero_of_size_le _ (by rw [transformedCore_size]; omega)

/-- **Keystone for `toMonic` inverse recovery.** Dilating the monic transform
`transformedCore core degree` by the leading coefficient recovers `core` scaled
by `leadingCoeff core ^ (degree - 1)`. The `1 ≤ degree` hypothesis is essential:
for a constant `core` the identity fails unless the leading coefficient is `1`.
Composed with `dilate_mul`, this is the inverse-factor correspondence the
recombination recovery proof rests on. -/
theorem dilate_transformedCore (core : ZPoly) (degree : Nat)
    (hdeg : 1 ≤ degree) (hcore : core.degree?.getD 0 = degree) :
    Hex.ZPoly.dilate (DensePoly.leadingCoeff core) (transformedCore core degree) =
      DensePoly.C (DensePoly.leadingCoeff core ^ (degree - 1)) * core := by
  have hsize_pos : 0 < core.size := by
    rcases Nat.eq_zero_or_pos core.size with hz | hpos
    · rw [show core.degree?.getD 0 = 0 by simp [DensePoly.degree?, hz]] at hcore
      omega
    · exact hpos
  have hsize : core.size = degree + 1 := by
    have hne : core.size ≠ 0 := by omega
    have hdeg' : core.degree?.getD 0 = core.size - 1 := by
      simp [DensePoly.degree?, hne]
    omega
  apply DensePoly.ext_coeff
  intro n
  rw [Hex.ZPoly.coeff_dilate, transformedCore_coeff, Hex.ZPoly.C_mul_eq_scale,
    DensePoly.coeff_scale_semiring]
  rcases Nat.lt_trichotomy n degree with h | h | h
  · rw [if_pos h]
    have hexp : n + (degree - 1 - n) = degree - 1 := by omega
    rw [← Int.mul_assoc,
      Int.mul_comm (DensePoly.leadingCoeff core ^ n) (core.coeff n),
      Int.mul_assoc, ← int_pow_add, hexp, Int.mul_comm]
  · rw [h, if_neg (Nat.lt_irrefl _), if_pos rfl, Int.mul_one]
    have hcoeff : core.coeff degree = DensePoly.leadingCoeff core := by
      rw [DensePoly.leadingCoeff_eq_coeff_last core hsize_pos, hsize, Nat.add_sub_cancel]
    rw [hcoeff, ← Lean.Grind.Semiring.pow_succ]
    congr 1
    omega
  · have hz : core.coeff n = 0 :=
      DensePoly.coeff_eq_zero_of_size_le core (by omega)
    rw [if_neg (by omega), if_neg (by omega), hz]
    simp

end ZPoly.ToMonicData

namespace ZPoly

/-- Public face of the inverse-recovery keystone, stated on the `toMonic` monic
field rather than the private `transformedCore`. For a core of degree `≥ 1`,
dilating `(toMonic core).monic` by the leading coefficient recovers `core`
scaled by `leadingCoeff core ^ (degree - 1)`. Holds in both the already-monic
and the genuine transform branch. -/
theorem dilate_monic_toMonic (core : ZPoly)
    (hdeg : 1 ≤ (toMonic core).degree) :
    Hex.ZPoly.dilate (DensePoly.leadingCoeff core) ((toMonic core).monic) =
      DensePoly.C (DensePoly.leadingCoeff core ^ ((toMonic core).degree - 1)) *
        core := by
  by_cases hmonic : DensePoly.leadingCoeff core = 1
  · have hmon : (toMonic core).monic = core :=
      toMonic_monic_eq_core_of_leadingCoeff_eq_one core hmonic
    rw [hmon, hmonic, Hex.ZPoly.dilate_one, Int.one_pow, Hex.ZPoly.C_mul_eq_scale]
    symm
    apply DensePoly.ext_coeff
    intro n
    rw [DensePoly.coeff_scale_semiring, Int.one_mul]
  · have hmon : (toMonic core).monic =
        ToMonicData.transformedCore core (core.degree?.getD 0) := by
      simp [toMonic, hmonic]
    have hdeg' : 1 ≤ core.degree?.getD 0 := by
      rw [toMonic_degree] at hdeg; exact hdeg
    rw [hmon, toMonic_degree]
    exact ToMonicData.dilate_transformedCore core (core.degree?.getD 0) hdeg' rfl

/-- Coefficient law for the monic transform `(toMonic core).monic` in the
genuine-transform branch (leading coefficient `≠ 1`).  Public face of the
private `ToMonicData.transformedCore_coeff`: below the top degree the
coefficient is `core.coeff i` scaled by a power of the leading coefficient, the
top coefficient is `1`, and higher coefficients vanish. -/
theorem toMonic_monic_coeff_of_leadingCoeff_ne_one (core : ZPoly)
    (hmonic : DensePoly.leadingCoeff core ≠ 1) (i : Nat) :
    (toMonic core).monic.coeff i =
      if i < core.degree?.getD 0 then
        core.coeff i * DensePoly.leadingCoeff core ^ (core.degree?.getD 0 - 1 - i)
      else if i = core.degree?.getD 0 then 1 else 0 := by
  rw [show (toMonic core).monic
        = ToMonicData.transformedCore core (core.degree?.getD 0) from by
      simp [toMonic, hmonic]]
  exact ToMonicData.transformedCore_coeff core (core.degree?.getD 0) i

/-- The monic transform preserves the recorded degree in all cases (sign-free,
unconditional companion to `toMonic_monic_degree_eq_of_pos_degree`). -/
theorem toMonic_monic_degree_getD (core : ZPoly) :
    (toMonic core).monic.degree?.getD 0 = core.degree?.getD 0 := by
  by_cases hmonic : DensePoly.leadingCoeff core = 1
  · rw [toMonic_monic_eq_core_of_leadingCoeff_eq_one core hmonic]
  · rw [show (toMonic core).monic
          = ToMonicData.transformedCore core (core.degree?.getD 0) from by
        simp [toMonic, hmonic]]
    exact ToMonicData.transformedCore_degree_getD core (core.degree?.getD 0)

/-- Stored size of the monic transform of a positive-degree core: one more than
the core degree, in both the already-monic and genuine-transform branches. -/
theorem toMonic_monic_size_of_pos_degree (core : ZPoly)
    (hdeg : 0 < core.degree?.getD 0) :
    (toMonic core).monic.size = core.degree?.getD 0 + 1 := by
  by_cases hmonic : DensePoly.leadingCoeff core = 1
  · rw [toMonic_monic_eq_core_of_leadingCoeff_eq_one core hmonic]
    have hsize_pos : 0 < core.size := by
      rcases Nat.eq_zero_or_pos core.size with h0 | h
      · exfalso
        rw [show core.degree?.getD 0 = 0 from by
          simp [DensePoly.degree?, h0]] at hdeg
        omega
      · exact h
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hsize_pos)
    rw [show core.degree?.getD 0 = core.size - 1 from by
      simp [DensePoly.degree?, hm]]
    omega
  · rw [show (toMonic core).monic
          = ToMonicData.transformedCore core (core.degree?.getD 0) from by
        simp [toMonic, hmonic]]
    exact ToMonicData.transformedCore_size core (core.degree?.getD 0)

end ZPoly

private theorem bhksIndicatorCandidatesStep_fold_preserves_prefix
    (f : ZPoly) (d : LiftData)
    (indicators : List (Array Int)) (acc candidates : Array ZPoly)
    (hfold :
      indicators.foldl (bhksIndicatorCandidatesStep f d) (some acc) =
        some candidates) :
    ∀ i, i < acc.size → candidates.getD i 0 = acc.getD i 0 := by
  induction indicators generalizing acc candidates with
  | nil =>
      intro i hi
      simp at hfold
      cases hfold
      rfl
  | cons indicator indicators ih =>
      intro i hi
      rw [List.foldl_cons] at hfold
      cases hhead : bhksIndicatorCandidate? f d indicator with
      | none =>
          have hnone := bhksIndicatorCandidatesStep_fold_none f d indicators
          simp [bhksIndicatorCandidatesStep, hhead, hnone] at hfold
      | some pair =>
          rcases pair with ⟨candidate, quotient⟩
          have hnext :
              indicators.foldl (bhksIndicatorCandidatesStep f d)
                  (some (acc.push candidate)) = some candidates := by
            simpa [bhksIndicatorCandidatesStep, hhead] using hfold
          have hprefix := ih (acc.push candidate) candidates hnext i
            (by simpa [Array.size_push] using Nat.lt_trans hi (Nat.lt_succ_self _))
          rw [hprefix]
          exact array_getD_push_lt acc candidate 0 hi

end Hex
