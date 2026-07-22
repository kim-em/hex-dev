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
public import HexBerlekampZassenhaus.WordCld
-- Needed so `decide`/`rfl` over `DensePoly`/`Array` equality reduces in the
-- kernel: the core `Array.instDecidableEq` delegates its nonempty case to the
-- non-`@[expose]` `Array.instDecidableEqImpl`, which is otherwise opaque under
-- the module system. Drop once that impl is exposed upstream (lean4).
import all Init.Data.Array.DecidableEq

public import HexBerlekampZassenhaus.ReassemblyProofs
public meta import HexBerlekampZassenhaus.ReassemblyProofs
import all HexBerlekampZassenhaus.PrimeSelection
import all HexBerlekampZassenhaus.Records
import all HexBerlekampZassenhaus.Certificate
import all HexBerlekampZassenhaus.ChoosePrimeData
import all HexBerlekampZassenhaus.ReassemblyProofs

public section
set_option backward.proofsInPublic true

/-!
This module collects the trial/root candidate definitions, centred-lift/CLD helpers, and the BHKS lattice basis.
-/
namespace Hex

/-- Non-monic converse to `exactQuotient?_product` for divisors with positive
leading coefficient.  Drops the `Monic` hypothesis from
`exactQuotient?_eq_some_of_mul_eq_monic_of_pos_degree` in favour of
`0 < leadingCoeff candidate`, routing the executable division through
`divMod_eq_of_pos_lc_pos_degree_mul_eq` and packaging the result with
`exactQuotient?_eq_some_of_divMod_eq_of_shouldRecord`.  Positive degree alone
discharges `shouldRecordPolynomialFactor`, since `0`, `C 1`, and `C (-1)` all
have `degree?.getD 0 = 0`. -/
theorem exactQuotient?_eq_some_of_pos_lc_pos_degree_mul_eq
    {target candidate quotient : ZPoly}
    (hpos_lc : 0 < DensePoly.leadingCoeff candidate)
    (hdegree : 0 < candidate.degree?.getD 0)
    (hmul : quotient * candidate = target) :
    exactQuotient? target candidate = some quotient := by
  have hrecord : shouldRecordPolynomialFactor candidate = true := by
    have hne_zero : candidate ≠ 0 := by
      intro hzero
      have hdeg : candidate.degree?.getD 0 = 0 := by
        rw [hzero]; simp [DensePoly.degree?]
      omega
    have hne_one : candidate ≠ 1 := by
      intro hone
      have hdeg : candidate.degree?.getD 0 = 0 := by
        rw [hone]
        change (DensePoly.C (1 : Int)).degree?.getD 0 = 0
        exact DensePoly.degree?_C_getD 1
      omega
    have hne_neg_one : candidate ≠ DensePoly.C (-1 : Int) := by
      intro hneg
      have hdeg : candidate.degree?.getD 0 = 0 := by
        rw [hneg]
        exact DensePoly.degree?_C_getD (-1)
      omega
    unfold shouldRecordPolynomialFactor
    simp [hne_zero, hne_one, hne_neg_one]
  have hdivMod_eq : DensePoly.divMod target candidate = (quotient, 0) :=
    ZPoly.divMod_eq_of_pos_lc_pos_degree_mul_eq target candidate quotient
      hpos_lc hdegree hmul
  exact exactQuotient?_eq_some_of_divMod_eq_of_shouldRecord hrecord hdivMod_eq hmul

private def positiveDivisors (n : Nat) : List Nat :=
  (List.range (n + 1)).filter fun d => d != 0 && n % d == 0

def integerRootCandidates (f : ZPoly) : List Int :=
  (positiveDivisors (f.coeff 0).natAbs).flatMap fun d =>
    let r : Int := Int.ofNat d
    [r, -r]

def linearFactorForRoot (r : Int) : ZPoly :=
  DensePoly.ofCoeffs #[-r, 1]

private theorem leadingCoeff_linearFactorForRoot (r : Int) :
    DensePoly.leadingCoeff (linearFactorForRoot r) = (1 : Int) := by
  unfold linearFactorForRoot
  rfl

private theorem linearFactorForRoot_size_eq_two (r : Int) :
    (linearFactorForRoot r).size = 2 := by
  unfold linearFactorForRoot
  rfl

private theorem linearFactorForRoot_degree_pos (r : Int) :
    0 < (linearFactorForRoot r).degree?.getD 0 := by
  unfold DensePoly.degree?
  rw [linearFactorForRoot_size_eq_two r]
  simp

private theorem linearFactorForRoot_ne_zero (r : Int) :
    linearFactorForRoot r ≠ (0 : ZPoly) := by
  intro h
  have hsize := linearFactorForRoot_size_eq_two r
  rw [h] at hsize
  change (0 : ZPoly).size = 2 at hsize
  have hzero : (0 : ZPoly).size = 0 := rfl
  omega

private theorem linearFactorForRoot_ne_one (r : Int) :
    linearFactorForRoot r ≠ (1 : ZPoly) := by
  intro h
  have hsize := linearFactorForRoot_size_eq_two r
  rw [h] at hsize
  have hone : (1 : ZPoly).size = 1 := rfl
  omega

private theorem linearFactorForRoot_ne_C_neg_one (r : Int) :
    linearFactorForRoot r ≠ DensePoly.C (-1 : Int) := by
  intro h
  have hsize := linearFactorForRoot_size_eq_two r
  rw [h] at hsize
  have hcsize : (DensePoly.C (-1 : Int)).size = 1 := rfl
  omega

private theorem normalizeFactorSign_linearFactorForRoot (r : Int) :
    normalizeFactorSign (linearFactorForRoot r) = linearFactorForRoot r := by
  unfold normalizeFactorSign
  rw [leadingCoeff_linearFactorForRoot]
  simp

private theorem shouldRecordPolynomialFactor_linearFactorForRoot (r : Int) :
    shouldRecordPolynomialFactor (linearFactorForRoot r) = true := by
  unfold shouldRecordPolynomialFactor
  simp [linearFactorForRoot_ne_zero, linearFactorForRoot_ne_one,
    linearFactorForRoot_ne_C_neg_one]

def splitIntegerRootFactorsAux :
    ZPoly → List Int → Nat → Array ZPoly × ZPoly
  | target, _roots, 0 => (#[], target)
  | target, [], _fuel + 1 => (#[], target)
  | target, root :: roots, fuel + 1 =>
      let factor := linearFactorForRoot root
      match exactQuotient? target factor with
      | some quotient =>
          let rest := splitIntegerRootFactorsAux quotient roots fuel
          (#[factor] ++ rest.1, rest.2)
      | none => splitIntegerRootFactorsAux target roots fuel

def quadraticIntegerRootFactors? (core : ZPoly) : Option (Array ZPoly) :=
  if core.degree?.getD 0 = 2 then
    let roots := integerRootCandidates core
    let split := splitIntegerRootFactorsAux core roots roots.length
    if split.1.size = 0 then
      none
    else if split.2 = 1 then
      some split.1
    else if split.2.degree?.getD 0 ≤ 1 then
      some (split.1.push split.2)
    else
      none
  else
    none

/-- Integer values in `[-B, B]`, listed in increasing order. -/
private def boundedIntegerList (B : Nat) : List Int :=
  (List.range (2 * B + 1)).map fun i => (Int.ofNat i) - (Int.ofNat B)

/-- All length-`len` integer coefficient lists with each entry in `[-B, B]`. -/
private def boundedCoefficientVectors (B : Nat) : Nat → List (List Int)
  | 0 => [[]]
  | len + 1 =>
      (boundedCoefficientVectors B len).flatMap fun rest =>
        (boundedIntegerList B).map fun c => c :: rest

/-- Bounded-coefficient candidate divisors of degree exactly `d`. Each
emitted polynomial has positive leading coefficient (so
`normalizeFactorSign` is the identity on it) and passes
`shouldRecordPolynomialFactor`. -/
private def trialDivisionCandidatesOfDegree (B d : Nat) : List ZPoly :=
  (boundedCoefficientVectors B (d + 1)).filterMap fun coeffs =>
    let p := DensePoly.ofCoeffs coeffs.toArray
    if p.degree?.getD 0 = d ∧ 0 < DensePoly.leadingCoeff p ∧
        shouldRecordPolynomialFactor p = true then
      some p
    else
      none

/-- Bounded-coefficient candidate divisors of degrees `1..maxDeg`, in order
of increasing degree. -/
private def trialDivisionCandidatesUpTo (B maxDeg : Nat) : List ZPoly :=
  (List.range maxDeg).flatMap fun d => trialDivisionCandidatesOfDegree B (d + 1)

/-- Peel candidate divisors off the running target via `exactQuotient?`. Each
candidate in the input list is tried at most once. Returns
`(emittedFactors, residual)` with the invariant
`residual * polyProduct emittedFactors = target`. -/
private def trialDivisionPeelAux :
    ZPoly → List ZPoly → Array ZPoly × ZPoly
  | target, [] => (#[], target)
  | target, candidate :: candidates =>
      match exactQuotient? target candidate with
      | some quotient =>
          let rest := trialDivisionPeelAux quotient candidates
          (#[candidate] ++ rest.1, rest.2)
      | none => trialDivisionPeelAux target candidates

/--
Standalone integer trial-division core for the slow factorization path.

First peels monic linear integer-root factors `(x - r)` off `core` via
`splitIntegerRootFactorsAux`, then enumerates non-unit polynomial candidates
of degrees `1..deg(afterLinear)/2` with coefficients in `[-B, B]`, dividing
each in turn into the running residual. The returned array consists of the
linear factors, the bounded-coefficient factors that exactly divided the
residual, and the final residual (omitted when it collapses to `1`).

The companion theorems `exhaustiveIntegerTrialCoreFactorsWithBound_polyProduct`,
`exhaustiveIntegerTrialCoreFactorsWithBound_normalizeFactorSign`, and
`exhaustiveIntegerTrialCoreFactorsWithBound_shouldRecord` record the
local executable invariants needed by the slow-path factorization
reassembly callers.
-/
def exhaustiveIntegerTrialCoreFactorsWithBound
    (core : ZPoly) (B : Nat) : Array ZPoly :=
  let split :=
    splitIntegerRootFactorsAux core (integerRootCandidates core)
      (integerRootCandidates core).length
  let peel :=
    trialDivisionPeelAux split.2
      (trialDivisionCandidatesUpTo B (split.2.degree?.getD 0 / 2))
  if peel.2 = 1 then
    split.1 ++ peel.1
  else
    (split.1 ++ peel.1).push peel.2

@[expose]
def centeredModNat (z : Int) (m : Nat) : Int :=
  if m = 0 then
    z
  else
    let r := z % Int.ofNat m
    if 2 * r.natAbs ≤ m then
      r
    else if r < 0 then
      r + Int.ofNat m
    else
      r - Int.ofNat m

theorem centeredModNat_zero (m : Nat) :
    centeredModNat 0 m = 0 := by
  unfold centeredModNat
  by_cases hm : m = 0 <;> simp [hm]

theorem centeredModNat_emod_eq_of_natAbs_le
    (z : Int) (m B : Nat)
    (hbound : z.natAbs ≤ B) (hsep : 2 * B < m) :
    centeredModNat (z % (m : Int)) m = z := by
  have hmpos : 0 < m := by omega
  have hmne : m ≠ 0 := Nat.ne_of_gt hmpos
  rcases Int.natAbs_eq z with hz | hz
  · rw [hz]
    have hltNat : z.natAbs < m := by omega
    have hlt : (z.natAbs : Int) < (m : Int) := by exact_mod_cast hltNat
    have hnonneg : 0 ≤ (z.natAbs : Int) := by exact_mod_cast Nat.zero_le z.natAbs
    have hmod : ((z.natAbs : Int) % (m : Int)) = (z.natAbs : Int) :=
      Int.emod_eq_of_lt hnonneg hlt
    unfold centeredModNat
    simp [hmne, hmod]
    intro hbad
    omega
  · rw [hz]
    by_cases hzero : z.natAbs = 0
    · simp [hzero, centeredModNat, hmne]
    · have ha_lt : z.natAbs < m := by omega
      have hrem : (-(z.natAbs : Int)) % (m : Int) = (m : Int) - (z.natAbs : Int) := by
        have hnonneg : 0 ≤ (m : Int) - (z.natAbs : Int) := by omega
        have hlt : (m : Int) - (z.natAbs : Int) < (m : Int) := by omega
        have hcongr :
            (((m : Int) - (z.natAbs : Int)) - (-(z.natAbs : Int))) % (m : Int) = 0 := by
          have hsimp :
              ((m : Int) - (z.natAbs : Int)) - (-(z.natAbs : Int)) = (m : Int) := by
            omega
          rw [hsimp]
          exact Int.emod_eq_zero_of_dvd ⟨1, by omega⟩
        have hmod_eq := (Int.emod_eq_emod_iff_emod_sub_eq_zero).2 hcongr
        rw [Int.emod_eq_of_lt hnonneg hlt] at hmod_eq
        exact hmod_eq.symm
      have hinner :
          (((m : Int) - (z.natAbs : Int)) % (m : Int)) =
            (m : Int) - (z.natAbs : Int) := by
        apply Int.emod_eq_of_lt <;> omega
      unfold centeredModNat
      simp [hmne, hrem, hinner]
      have hsub_cast : (m : Int) - (z.natAbs : Int) = (m - z.natAbs : Nat) := by
        omega
      have hnatAbs : (((m : Int) - (z.natAbs : Int)).natAbs) = m - z.natAbs := by
        rw [hsub_cast, Int.natAbs_natCast]
      rw [hnatAbs]
      have hnot : ¬ 2 * (m - z.natAbs) ≤ m := by omega
      simp [hnot]
      have hnotneg : ¬ (m : Int) - (z.natAbs : Int) < 0 := by omega
      simp [hnotneg]
      omega

/-- Centred residue modulo `p^b`, the `mod^±` operation in the BHKS cut. -/
@[expose]
def centeredResiduePow (p b : Nat) (x : Int) : Int :=
  centeredModNat x (p ^ b)

/--
BHKS two-sided cut `Psi^a_b(x) = (x_amb - (x_amb mod^± p^b)) / p^b`, where
`x_amb := x mod^± p^a` is the centered ambient representative.

Centering at the ambient modulus `p^a` before taking the lower-precision cut
is required to match the SPEC semantics: a CLD coefficient passed in as a
nonnegative `p^a`-residue `(p^a - c)` of a negative exact value `-c` must be
recentered to `-c` before applying the `p^b` cut. Without this step the cut
produces an oversized output for negative exact coefficients — see #6217 for
the `f = x^2 - 5*x + 6`, `g = x - 2`, `p = 5`, `a = 6` counterexample to the
old uncentered formulation.
-/
def psiCut (p a b : Nat) (x : Int) : Int :=
  let modulus := p ^ b
  if modulus = 0 then
    0
  else
    let xCentered := centeredResiduePow p a x
    (xCentered - centeredResiduePow p b xCentered) / Int.ofNat modulus

/-- Bignum reference for `cldQuotientMod`: reduce `f * g' / g` modulo `p^a`
using `Int` polynomial arithmetic. This is the specification the word-sized
fast path is proven byte-identical to (`cldQuotientMod_eq_spec`). -/
@[expose]
def cldQuotientModBignum (f g : ZPoly) (p a : Nat) : ZPoly :=
  let numerator := ZPoly.reduceModPow (f * DensePoly.derivative g) p a
  let quotient := (DensePoly.divMod numerator g).1
  ZPoly.reduceModPow quotient p a

/--
Mod-`p^a` representative of `f * g.derivative / g`, the polynomial whose
`x^j` coefficient is the integer CLD coefficient `[x^j] Phi(g)` reduced
modulo `p^a`.

Exposed (rather than private) so the BHKS bridge layer can state the
congruence linking the executable quotient to the exact integer CLD
coefficient.
-/
@[expose]
def cldQuotientMod (f g : ZPoly) (p a : Nat) : ZPoly :=
  -- Word-sized fast path: when `p^a` fits an odd machine word and `g` is a monic
  -- divisor of positive degree, `cldQuotientModWord?` computes the identical
  -- quotient over `WordMod` (single-reduction Montgomery). The byte-identical
  -- correspondence is `cldQuotientModWord?_eq`; `cldQuotientMod_eq_spec` proves
  -- this dispatch equals `cldQuotientModBignum` for every input.
  match powLtWord? p a with
  | some m =>
      if (UInt64.ofNat m) % 2 = 1 ∧ 1 < m ∧
          g.leadingCoeff = 1 ∧ 0 < g.degree?.getD 0 then
        (cldQuotientModWord? f g p a).getD (cldQuotientModBignum f g p a)
      else cldQuotientModBignum f g p a
  | none => cldQuotientModBignum f g p a

/--
Centred high-bit CLD coefficients for one lifted local factor.

The returned array has one entry for each coefficient index
`0, ..., deg(f)-1`; entry `j` is
`Psi^a_{ell_j}([x^j] (f * g.derivative / g mod p^a))`.
-/
def cldCoeffs (f : ZPoly) (p a : Nat) (g : ZPoly) : Array Int :=
  let quotient := cldQuotientMod f g p a
  let n := f.degree?.getD 0
  (List.range n).map
    (fun j => psiCut p a (bhksCoeffCutThreshold p f j) (quotient.coeff j))
    |>.toArray

/--
Aggregate BHKS CLD tail entry for a selected family of lifted local factors.

Unlike `cldCoeffs`, this cuts once after summing the selected
`cldQuotientMod` coefficients.  This is the shape needed by the BHKS true-factor
support column: wraparound is controlled on the aggregate residue, not on the
sum of separately cut per-factor residues.
-/
def aggregateCldTail (f : ZPoly) (p a j : Nat) (selectedFactors : Array ZPoly) : Int :=
  let quotientSum :=
    selectedFactors.foldl
      (fun acc g => acc + cldQuotientMod f g p a) (0 : ZPoly)
  psiCut p a (bhksCoeffCutThreshold p f j) (quotientSum.coeff j)

/-- `centeredModNat` depends only on its argument modulo `m`. -/
theorem centeredModNat_emod_self (z : Int) (m : Nat) :
    centeredModNat (z % (m : Int)) m = centeredModNat z m := by
  by_cases hm : m = 0
  · subst hm
    show centeredModNat (z % ((0 : Nat) : Int)) 0 = centeredModNat z 0
    simp [Int.emod_zero]
  · have hmod : (z % (m : Int)) % Int.ofNat m = z % Int.ofNat m := by
      show z % Int.ofNat m % Int.ofNat m = z % Int.ofNat m
      exact Int.emod_emod _ _
    unfold centeredModNat
    rw [if_neg hm, if_neg hm, hmod]

/-- `centeredModNat` chooses a representative congruent to the input modulo `m`. -/
theorem self_sub_centeredModNat_dvd (z : Int) (m : Nat) :
    (m : Int) ∣ z - centeredModNat z m := by
  by_cases hm : m = 0
  · subst hm
    simp [centeredModNat]
  · let r : Int := z % (m : Int)
    have hr_dvd : (m : Int) ∣ z - r := by
      have hmod : z % (m : Int) = r % (m : Int) := by
        simp [r]
      exact Int.dvd_of_emod_eq_zero
        ((Int.emod_eq_emod_iff_emod_sub_eq_zero).mp hmod)
    unfold centeredModNat
    simp only [hm, ↓reduceIte]
    by_cases hsmall : 2 * (z % (m : Int)).natAbs ≤ m
    · simpa [hsmall, r] using hr_dvd
    · by_cases hneg : z % (m : Int) < 0
      · obtain ⟨t, ht⟩ := hr_dvd
        refine ⟨t - 1, ?_⟩
        grind
      · obtain ⟨t, ht⟩ := hr_dvd
        refine ⟨t + 1, ?_⟩
        grind

/--
The BHKS cut decomposes the centered ambient representative into a lower
centered residue plus `p^b` times the high-bit cut coefficient.
-/
theorem centeredResiduePow_add_pow_mul_psiCut
    (p a b : Nat) (z : Int) (hmod : p ^ b ≠ 0) :
    centeredResiduePow p a z =
      centeredResiduePow p b (centeredResiduePow p a z) +
        ((p ^ b : Nat) : Int) * psiCut p a b z := by
  unfold psiCut
  rw [if_neg hmod]
  let xCentered := centeredResiduePow p a z
  let lower := centeredResiduePow p b xCentered
  have hdvd : ((p ^ b : Nat) : Int) ∣ xCentered - lower := by
    have h := self_sub_centeredModNat_dvd xCentered (p ^ b)
    simpa [lower, centeredResiduePow] using h
  obtain ⟨t, ht⟩ := hdvd
  have hdiv : (xCentered - lower) / ((p ^ b : Nat) : Int) = t := by
    rw [ht, Int.mul_ediv_cancel_left]
    exact_mod_cast hmod
  change xCentered = lower +
    ((p ^ b : Nat) : Int) * ((xCentered - lower) / ((p ^ b : Nat) : Int))
  rw [hdiv]
  omega

/--
If `y` is an exact integer with `|y| ≤ B`, `y ≡ z (mod p^a)`, and the ambient
modulus `p^a` is large enough to separate the centered residue (`2*B < p^a`),
then `centeredResiduePow p a z = y`.
-/
theorem centeredResiduePow_eq_of_natAbs_le
    (p a : Nat) (y z : Int) (B : Nat)
    (hbound : y.natAbs ≤ B)
    (hsep : 2 * B < p ^ a)
    (hcongr : y % ((p ^ a : Nat) : Int) = z % ((p ^ a : Nat) : Int)) :
    centeredResiduePow p a z = y := by
  unfold centeredResiduePow
  rw [← centeredModNat_emod_self z, ← hcongr]
  exact centeredModNat_emod_eq_of_natAbs_le y (p ^ a) B hbound hsep

/--
If an exact integer `y` with `|y| ≤ B` is congruent to `z` modulo `p^a`, and
both the ambient modulus `p^a` and the lower cut modulus `p^b` separate `B`
(`2*B < p^a` and `2*B < p^b`), then the BHKS two-sided cut `psiCut p a b z`
vanishes.
-/
theorem psiCut_eq_zero_of_natAbs_le
    (p a b : Nat) (y z : Int) (B : Nat)
    (hbound : y.natAbs ≤ B)
    (hsep_a : 2 * B < p ^ a)
    (hsep_b : 2 * B < p ^ b)
    (hcongr : y % ((p ^ a : Nat) : Int) = z % ((p ^ a : Nat) : Int)) :
    psiCut p a b z = 0 := by
  unfold psiCut
  have hbpos : 0 < p ^ b := by omega
  have hbne : (p ^ b : Nat) ≠ 0 := Nat.ne_of_gt hbpos
  have hcentered_amb : centeredResiduePow p a z = y :=
    centeredResiduePow_eq_of_natAbs_le p a y z B hbound hsep_a hcongr
  rw [if_neg hbne]
  show (centeredResiduePow p a z - centeredResiduePow p b (centeredResiduePow p a z))
      / Int.ofNat (p ^ b) = 0
  rw [hcentered_amb]
  have hcentered_b : centeredResiduePow p b y = y := by
    unfold centeredResiduePow
    rw [← centeredModNat_emod_self y]
    exact centeredModNat_emod_eq_of_natAbs_le y (p ^ b) B hbound hsep_b
  rw [hcentered_b, Int.sub_self, Int.zero_ediv]

/--
Absolute-value form of `psiCut_eq_zero_of_natAbs_le`: under the same
hypotheses, `|psiCut p a b z| ≤ B`. Useful when callers carry the BHKS
column bound `B = bhksCoeffBound f j` and just need an upper bound on the
executable cut output.
-/
theorem abs_psiCut_le_of_natAbs_le
    (p a b : Nat) (y z : Int) (B : Nat)
    (hbound : y.natAbs ≤ B)
    (hsep_a : 2 * B < p ^ a)
    (hsep_b : 2 * B < p ^ b)
    (hcongr : y % ((p ^ a : Nat) : Int) = z % ((p ^ a : Nat) : Int)) :
    (psiCut p a b z).natAbs ≤ B := by
  rw [psiCut_eq_zero_of_natAbs_le p a b y z B hbound hsep_a hsep_b hcongr]
  exact Nat.zero_le _

/--
In-range coordinate of `cldCoeffs`: for `j < deg(f)`, the executable
`cldCoeffs` array entry is exactly `psiCut` applied to the corresponding
quotient coefficient.
-/
theorem cldCoeffs_getD_of_lt
    (f : ZPoly) (p a : Nat) (g : ZPoly) (j : Nat)
    (h : j < f.degree?.getD 0) :
    (cldCoeffs f p a g).getD j 0 =
      psiCut p a (bhksCoeffCutThreshold p f j) ((cldQuotientMod f g p a).coeff j) := by
  unfold cldCoeffs
  rw [Array.getD_eq_getD_getElem?]
  have hlen :
      ((List.range (f.degree?.getD 0)).map (fun j =>
        psiCut p a (bhksCoeffCutThreshold p f j)
          ((cldQuotientMod f g p a).coeff j))).length = f.degree?.getD 0 := by
    simp
  have hsize :
      ((List.range (f.degree?.getD 0)).map (fun j =>
        psiCut p a (bhksCoeffCutThreshold p f j)
          ((cldQuotientMod f g p a).coeff j))).toArray.size = f.degree?.getD 0 := by
    simp [hlen]
  rw [Array.getElem?_eq_getElem (by simpa [hsize] using h)]
  simp [List.getElem_toArray, List.getElem_map, List.getElem_range]

/-- In-range CLD coefficients are the high-bit part of `cldQuotientMod`. -/
theorem cldQuotientMod_coeff_decomp_of_lt
    (f g : ZPoly) (p a j : Nat)
    (hj : j < f.degree?.getD 0)
    (hb : p ^ bhksCoeffCutThreshold p f j ≠ 0) :
    centeredResiduePow p a ((cldQuotientMod f g p a).coeff j) =
      centeredResiduePow p (bhksCoeffCutThreshold p f j)
          (centeredResiduePow p a ((cldQuotientMod f g p a).coeff j)) +
        ((p ^ bhksCoeffCutThreshold p f j : Nat) : Int) *
          (cldCoeffs f p a g).getD j 0 := by
  rw [cldCoeffs_getD_of_lt f p a g j hj]
  exact centeredResiduePow_add_pow_mul_psiCut p a (bhksCoeffCutThreshold p f j)
    ((cldQuotientMod f g p a).coeff j) hb

/-- Euclidean reconstruction for the division underlying `cldQuotientMod`: for a
monic divisor `g`, the raw quotient and remainder of `numerator / g` recompose
`numerator`, where `numerator = (f * g') mod p^a` is the dividend `cldQuotientMod`
feeds to `DensePoly.divMod` before its own mod-`p^a` reduction of the quotient.
The downstream modular-congruence bridge reduces this exact identity mod `p^a`. -/
theorem cldQuotientMod_divMod_reconstruction (f g : ZPoly) (p a : Nat)
    (hg : DensePoly.Monic g) :
    let numerator := ZPoly.reduceModPow (f * DensePoly.derivative g) p a
    (DensePoly.divMod numerator g).1 * g + (DensePoly.divMod numerator g).2
      = numerator :=
  ZPoly.divMod_reconstruction_of_monic _ g hg

/-- Per-coordinate BHKS cut thresholds for the all-coefficients CLD lattice. -/
@[expose]
def bhksCutThresholds (f : ZPoly) (p : Nat) : Array Nat :=
  let n := f.degree?.getD 0
  (List.range n).map (fun j => bhksCoeffCutThreshold p f j) |>.toArray

/-- In-range BHKS cut thresholds are the per-coordinate `bhksCoeffCutThreshold`. -/
theorem bhksCutThresholds_getD_of_lt (f : ZPoly) (p j : Nat)
    (h : j < f.degree?.getD 0) :
    (bhksCutThresholds f p).getD j 0 = bhksCoeffCutThreshold p f j := by
  unfold bhksCutThresholds
  rw [Array.getD_eq_getD_getElem?]
  have hsize :
      ((List.range (f.degree?.getD 0)).map
        (fun j => bhksCoeffCutThreshold p f j)).toArray.size = f.degree?.getD 0 := by
    simp
  rw [Array.getElem?_eq_getElem (by simpa [hsize] using h)]
  simp [List.getElem_toArray, List.getElem_map, List.getElem_range]

/--
Executable row-basis data for the BHKS all-coefficients CLD lattice.

The basis has row and column dimension `factorCount + coeffWidth`. Its first
`factorCount` columns are indicator coordinates, and its remaining
`coeffWidth` columns are CLD high-bit coordinates.
-/
structure BhksLatticeBasis where
  p : Nat
  precision : Nat
  factorCount : Nat
  coeffWidth : Nat
  liftedFactors : Array ZPoly
  cutThresholds : Array Nat
  cldRows : Array (Array Int)
  basis : Matrix Int (factorCount + coeffWidth) (factorCount + coeffWidth)

/--
Projected BHKS rows after LLL reduction and the Gram-Schmidt cut.

`cutRadiusSq4` stores `4 * B'^2 = 4r + n*r^2`, avoiding square-root or
floating-point arithmetic for the BHKS cut radius.
-/
structure BhksProjectedRows where
  factorCount : Nat
  coeffWidth : Nat
  cutRadiusSq4 : Nat
  reducedRowCount : Nat
  projectedRows : Array (Array Int)

@[expose]
def bhksLatticeEntry
    (r n p a : Nat) (thresholds : Array Nat) (cldRows : Array (Array Int))
    (i j : Fin (r + n)) : Int :=
  if _hi : i.val < r then
    if _hj : j.val < r then
      if i.val = j.val then 1 else 0
    else
      (cldRows.getD i.val #[]).getD (j.val - r) 0
  else if _hj : j.val < r then
    0
  else
    let coord := i.val - r
    if j.val - r = coord then
      Int.ofNat (p ^ (a - thresholds.getD coord 0))
    else
      0

/--
Build the BHKS all-coefficients CLD row-basis matrix
`[ I_r | A_tilde ; 0 | diag(p^(a-l_j)) ]`.

The diagonal exponent uses natural subtraction; callers that need the exact
BHKS hypotheses should lift to a precision `a` satisfying every `l_j ≤ a`.
-/
@[expose]
def bhksLatticeBasis (f : ZPoly) (p a : Nat) (liftedFactors : Array ZPoly) :
    BhksLatticeBasis :=
  let r := liftedFactors.size
  let n := f.degree?.getD 0
  let thresholds := bhksCutThresholds f p
  let cldRows := liftedFactors.map (fun g => cldCoeffs f p a g)
  let basis : Matrix Int (r + n) (r + n) :=
    Matrix.ofFn (bhksLatticeEntry r n p a thresholds cldRows)
  { p
    precision := a
    factorCount := r
    coeffWidth := n
    liftedFactors
    cutThresholds := thresholds
    cldRows
    basis }

private theorem bhksLatticeBasis_factorCount_eq
    (f : ZPoly) (p a : Nat) (liftedFactors : Array ZPoly) :
    (bhksLatticeBasis f p a liftedFactors).factorCount = liftedFactors.size := by
  rfl

private theorem bhksLatticeBasis_coeffWidth_eq
    (f : ZPoly) (p a : Nat) (liftedFactors : Array ZPoly) :
    (bhksLatticeBasis f p a liftedFactors).coeffWidth = f.degree?.getD 0 := by
  rfl

theorem bhksLatticeEntry_topLeft
    (r n p a : Nat) (thresholds : Array Nat) (cldRows : Array (Array Int))
    (i j : Fin (r + n)) (hi : i.val < r) (hj : j.val < r) :
    bhksLatticeEntry r n p a thresholds cldRows i j =
      if i.val = j.val then 1 else 0 := by
  simp [bhksLatticeEntry, hi, hj]

theorem bhksLatticeEntry_bottomLeft
    (r n p a : Nat) (thresholds : Array Nat) (cldRows : Array (Array Int))
    (i j : Fin (r + n)) (hi : r ≤ i.val) (hj : j.val < r) :
    bhksLatticeEntry r n p a thresholds cldRows i j = 0 := by
  have hnot : ¬i.val < r := by
    omega
  simp [bhksLatticeEntry, hnot, hj]

theorem bhksLatticeEntry_bottomRight
    (r n p a : Nat) (thresholds : Array Nat) (cldRows : Array (Array Int))
    (i j : Fin (r + n)) (hi : r ≤ i.val) (hj : r ≤ j.val) :
    bhksLatticeEntry r n p a thresholds cldRows i j =
      let coord := i.val - r
      if j.val - r = coord then
        Int.ofNat (p ^ (a - thresholds.getD coord 0))
      else
        0 := by
  have hnot_i : ¬i.val < r := by
    omega
  have hnot_j : ¬j.val < r := by
    omega
  simp [bhksLatticeEntry, hnot_i, hnot_j]

theorem bhksLatticeEntry_bottomRight_offDiag
    (r n p a : Nat) (thresholds : Array Nat) (cldRows : Array (Array Int))
    (i j : Fin (r + n)) (hi : r ≤ i.val) (hj : r ≤ j.val)
    (hneq : j.val - r ≠ i.val - r) :
    bhksLatticeEntry r n p a thresholds cldRows i j = 0 := by
  rw [bhksLatticeEntry_bottomRight r n p a thresholds cldRows i j hi hj]
  simp [hneq]

theorem bhksLatticeEntry_bottomRight_diag
    (r n p a : Nat) (thresholds : Array Nat) (cldRows : Array (Array Int))
    (i : Fin (r + n)) (hi : r ≤ i.val) :
    bhksLatticeEntry r n p a thresholds cldRows i i =
      Int.ofNat (p ^ (a - thresholds.getD (i.val - r) 0)) := by
  rw [bhksLatticeEntry_bottomRight r n p a thresholds cldRows i i hi hi]
  simp

theorem bhksLatticeEntry_bottomRight_diag_pos
    (r n p a : Nat) (thresholds : Array Nat) (cldRows : Array (Array Int))
    (hp : 0 < p) (i : Fin (r + n)) (hi : r ≤ i.val)
    (_hthreshold : thresholds.getD (i.val - r) 0 ≤ a) :
    0 < bhksLatticeEntry r n p a thresholds cldRows i i := by
  rw [bhksLatticeEntry_bottomRight_diag r n p a thresholds cldRows i hi]
  have hpos : 0 < p ^ (a - thresholds.getD (i.val - r) 0) :=
    Nat.pow_pos hp
  exact Int.ofNat_lt.mpr hpos

/-- Four times the squared BHKS cut radius, `4 * (r + n * (r / 2)^2)`. -/
@[expose]
def bhksCutRadiusSq4 (L : BhksLatticeBasis) : Nat :=
  4 * L.factorCount + L.coeffWidth * L.factorCount * L.factorCount

@[expose]
def bhksWithinGramSchmidtCut (L : BhksLatticeBasis)
    (dets : Vector Nat (L.factorCount + L.coeffWidth + 1))
    (i : Fin (L.factorCount + L.coeffWidth)) : Bool :=
  let d0 := dets.get ⟨i.val,
    Nat.lt_trans i.isLt (Nat.lt_succ_self (L.factorCount + L.coeffWidth))⟩
  let d1 := dets.get ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
  if d0 = 0 then
    false
  else
    4 * ((d1 : Rat) / (d0 : Rat)) ≤ (bhksCutRadiusSq4 L : Rat)

@[expose]
def bhksProjectIndicator (r n : Nat) (v : Vector Int (r + n)) : Array Int :=
  (List.range r).map
    (fun j =>
      if h : j < r + n then
        v.get ⟨j, h⟩
      else
        0)
    |>.toArray

def bhksRowsArrayToMatrix {m : Nat} (n : Nat) (rows : Array (Vector Int m)) :
    Matrix Int n m :=
  Matrix.ofFn fun i j => (rows.getD i.val (Vector.ofFn fun _ => 0))[j]

theorem bhksRowsArrayToMatrix_row {m n : Nat} (rows : Array (Vector Int m))
    (i : Fin n) :
    Matrix.row (bhksRowsArrayToMatrix n rows) i =
      rows.getD i.val (Vector.ofFn fun _ => 0) := by
  apply Vector.ext
  intro j hj
  show (bhksRowsArrayToMatrix n rows)[i][(⟨j, hj⟩ : Fin m)] = _
  rw [bhksRowsArrayToMatrix, Hex.Matrix.getElem_ofFn]
  rfl

theorem bhksRowsArrayToMatrix_toArray {m n : Nat} (B : Matrix Int n m) :
    bhksRowsArrayToMatrix n B.rows.toArray = B := by
  apply Hex.Matrix.ext_getElem
  intro i j
  rw [bhksRowsArrayToMatrix, Hex.Matrix.getElem_ofFn]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simp)]
  simp [Hex.Matrix.getElem_rows]

theorem lll_delta_lower : (1 / 4 : Rat) < 3 / 4 := by
  grind

theorem lll_delta_upper : (3 / 4 : Rat) ≤ 1 := by
  grind

/--
Length of the BHKS Lemma 5.7 *prefix* cut: one past the last Gram-Schmidt
index whose squared length is within the radius (`0` if none passes).  Because
the fold runs in increasing index order, the accumulator ends at
`(max { i : ‖b*_i‖² ≤ radius }) + 1`, so retaining indices `< t` keeps the
contiguous prefix `b_0 … b_t` in original order — including earlier rows whose
own Gram-Schmidt norm exceeds the radius.
-/
@[expose]
def bhksCutPrefixCount
    (L : BhksLatticeBasis)
    (reduced : Matrix Int (L.factorCount + L.coeffWidth)
        (L.factorCount + L.coeffWidth)) :
    Nat :=
  let dets := GramSchmidt.Int.gramDetVec reduced
  (List.finRange (L.factorCount + L.coeffWidth)).foldl
    (fun acc i =>
      if bhksWithinGramSchmidtCut L dets i then i.val + 1 else acc)
    0

@[expose]
def bhksCutProjectReducedRows
    (L : BhksLatticeBasis)
    (reduced : Matrix Int (L.factorCount + L.coeffWidth)
        (L.factorCount + L.coeffWidth)) :
    Array (Array Int) :=
  let t := bhksCutPrefixCount L reduced
  (List.finRange (L.factorCount + L.coeffWidth)).foldl
    (fun acc i =>
      if i.val < t then
        acc.push (bhksProjectIndicator L.factorCount L.coeffWidth (reduced.row i))
      else
        acc)
    #[]

def bhksRetainedRowIndices
    (L : BhksLatticeBasis)
    (reduced : Matrix Int (L.factorCount + L.coeffWidth)
        (L.factorCount + L.coeffWidth)) :
    Array (Fin (L.factorCount + L.coeffWidth)) :=
  let t := bhksCutPrefixCount L reduced
  (List.finRange (L.factorCount + L.coeffWidth)).foldl
    (fun acc i =>
      if i.val < t then
        acc.push i
      else
        acc)
    #[]

def bhksProjectRetainedRows
    (L : BhksLatticeBasis)
    (reduced : Matrix Int (L.factorCount + L.coeffWidth)
        (L.factorCount + L.coeffWidth))
    (indices : Array (Fin (L.factorCount + L.coeffWidth))) :
    Array (Array Int) :=
  indices.map fun i => bhksProjectIndicator L.factorCount L.coeffWidth (reduced.row i)

/--
Proof-facing trace for the executable BHKS projected-row construction.  It
records the unchecked LLL rows, their matrix view, the Gram determinant vector
used by the cut, the retained source row indices, and the projected retained
rows.  `bhksProjectedRows` below is the old compact projection of this trace.
-/
structure BhksProjectedRowsTrace (L : BhksLatticeBasis) where
  reducedRows : Array (Vector Int (L.factorCount + L.coeffWidth))
  reducedMatrix : Matrix Int (L.factorCount + L.coeffWidth)
      (L.factorCount + L.coeffWidth)
  gramDets : Vector Nat (L.factorCount + L.coeffWidth + 1)
  retainedIndices : Array (Fin (L.factorCount + L.coeffWidth))
  projectedRetainedRows : Array (Array Int)
  projectedRows : Array (Array Int)

@[expose]
def bhksProjectedRowsTrace (L : BhksLatticeBasis)
    (hrows : 1 ≤ L.factorCount + L.coeffWidth) : BhksProjectedRowsTrace L :=
  let reducedRows :=
    lllNative.shortVectors L.basis (3 / 4) lll_delta_lower lll_delta_upper hrows
  let reducedMatrix :=
    bhksRowsArrayToMatrix (L.factorCount + L.coeffWidth) reducedRows
  let retainedIndices := bhksRetainedRowIndices L reducedMatrix
  { reducedRows
    reducedMatrix
    gramDets := GramSchmidt.Int.gramDetVec reducedMatrix
    retainedIndices
    projectedRetainedRows := bhksProjectRetainedRows L reducedMatrix retainedIndices
    projectedRows := bhksCutProjectReducedRows L reducedMatrix }

theorem bhksProjectedRowsTrace_reducedMatrix_eq
    (L : BhksLatticeBasis) (hrows : 1 ≤ L.factorCount + L.coeffWidth) :
    (bhksProjectedRowsTrace L hrows).reducedMatrix =
      lllNative L.basis (3 / 4) lll_delta_lower lll_delta_upper hrows := by
  simp [bhksProjectedRowsTrace, lllNative.shortVectors, bhksRowsArrayToMatrix_toArray]

/--
Run LLL on a BHKS row-basis lattice, discard rows whose Gram-Schmidt squared
length exceeds the BHKS radius, and project survivors to the first `r`
indicator coordinates. The squared Gram-Schmidt lengths are computed from the
integer leading Gram determinant vector as `d_{i+1}/d_i`.

The result is the executable `L'` row data consumed by the later RREF /
equivalence-class recovery stage.
-/
@[expose]
def bhksProjectedRows (L : BhksLatticeBasis)
    (hrows : 1 ≤ L.factorCount + L.coeffWidth) : BhksProjectedRows :=
  let reducedRows :=
    lllNative.shortVectors L.basis (3 / 4) lll_delta_lower lll_delta_upper hrows
  let reducedBasis :=
    bhksRowsArrayToMatrix (L.factorCount + L.coeffWidth) reducedRows
  { factorCount := L.factorCount
    coeffWidth := L.coeffWidth
    cutRadiusSq4 := bhksCutRadiusSq4 L
    reducedRowCount := reducedRows.size
    projectedRows := bhksCutProjectReducedRows L reducedBasis }

theorem bhksProjectedRows_eq_trace
    (L : BhksLatticeBasis) (hrows : 1 ≤ L.factorCount + L.coeffWidth) :
    bhksProjectedRows L hrows =
      { factorCount := L.factorCount
        coeffWidth := L.coeffWidth
        cutRadiusSq4 := bhksCutRadiusSq4 L
        reducedRowCount := (bhksProjectedRowsTrace L hrows).reducedRows.size
        projectedRows := (bhksProjectedRowsTrace L hrows).projectedRows } := by
  simp [bhksProjectedRows, bhksProjectedRowsTrace]

#guard psiCut 5 4 1 3 = 1
#guard psiCut 5 4 1 3 ≠ 3 / (5 : Int)
#guard centeredResiduePow 5 1 (-3) = 2
#guard psiCut 5 4 1 (-3) = -1
#guard centeredResiduePow 5 1 (-2) = -2
#guard psiCut 5 4 1 (-2) = 0
#guard psiCut 5 4 1 (-2) ≠ (-2) / (5 : Int)

private def cldGuardF : ZPoly :=
  DensePoly.ofCoeffs #[6, -5, 1]

end Hex
