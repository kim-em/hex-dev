import HexBerlekampZassenhaus.Basic
import HexBerlekampZassenhausMathlib.Lattice
import HexBerlekampZassenhausMathlib.Resultant

/-!
Abstract resultant/divisibility layer for the BHKS bad-vector argument.

The executable CLD/lattice objects are deliberately absent from this module.
Later BHKS termination work can instantiate `BadVectorResultantData` with the
polynomial associated to a lattice vector, then use the packaged lower and
upper bounds without reopening the resultant API.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

/--
Proof-facing data carried by the BHKS bad-vector route.

`f` is the input polynomial and `H` is the auxiliary polynomial extracted from
the bad vector.  The hypotheses say that the transported pair is coprime over
`ℚ` and that the modular construction forces a `p^(a*d)` divisibility of the
integer resultant.
-/
structure BadVectorResultantData where
  f : Polynomial ℤ
  H : Polynomial ℤ
  p : Nat
  a : Nat
  d : Nat
  p_pos : 0 < p
  d_pos : 0 < d
  coprime_over_rat :
    IsCoprime (f.map (Int.castRingHom ℚ)) (H.map (Int.castRingHom ℚ))
  resultant_divisible :
    ((p ^ (a * d) : Nat) : ℤ) ∣ Polynomial.resultant f H

namespace BadVectorResultantData

/-- The integer resultant attached to bad-vector proof data. -/
def resultant (D : BadVectorResultantData) : ℤ :=
  Polynomial.resultant D.f D.H

/-- The modular lower-bound divisor attached to bad-vector proof data. -/
def divisor (D : BadVectorResultantData) : Nat :=
  D.p ^ (D.a * D.d)

theorem resultant_ne_zero (D : BadVectorResultantData) :
    D.resultant ≠ 0 := by
  exact int_resultant_ne_zero_of_coprime_over_rat D.f D.H D.coprime_over_rat

theorem divisor_pos (D : BadVectorResultantData) :
    0 < D.divisor := by
  exact pow_pos D.p_pos _

/--
The modular divisibility hypothesis gives the arithmetic lower bound on the
absolute value of the nonzero integer resultant.
-/
theorem divisor_le_resultant_natAbs (D : BadVectorResultantData) :
    D.divisor ≤ Int.natAbs D.resultant := by
  have hdiv : ((D.divisor : Nat) : ℤ) ∣ D.resultant := by
    simpa [divisor, resultant] using D.resultant_divisible
  have hnonzero : D.resultant ≠ 0 := D.resultant_ne_zero
  simpa [divisor] using Int.natAbs_le_of_dvd_ne_zero hdiv hnonzero

/--
Real-valued lower bound used when comparing the BHKS modular divisibility
against Hadamard's resultant upper bound.
-/
theorem divisor_real_le_abs_resultant (D : BadVectorResultantData) :
    (D.divisor : ℝ) ≤ |((D.resultant : ℤ) : ℝ)| := by
  have h : (D.divisor : ℝ) ≤ (Int.natAbs D.resultant : ℝ) := by
    exact_mod_cast D.divisor_le_resultant_natAbs
  simpa [Nat.cast_natAbs] using h

/-- Existing Sylvester/Hadamard bound specialized to bad-vector data. -/
theorem abs_resultant_le_l2norm_pow (D : BadVectorResultantData) :
    |((D.resultant : ℤ) : ℝ)| ≤
      (HexPolyZMathlib.l2norm D.f) ^ D.H.natDegree *
        (HexPolyZMathlib.l2norm D.H) ^ D.f.natDegree := by
  simpa [resultant] using
    HexBerlekampZassenhausMathlib.abs_resultant_le_l2norm_pow D.f D.H

/--
Combined BHKS bad-vector resultant comparison: the modular lower bound is at
most the Hadamard/l2norm upper bound.
-/
theorem divisor_real_le_l2norm_pow (D : BadVectorResultantData) :
    (D.divisor : ℝ) ≤
      (HexPolyZMathlib.l2norm D.f) ^ D.H.natDegree *
        (HexPolyZMathlib.l2norm D.H) ^ D.f.natDegree :=
  le_trans D.divisor_real_le_abs_resultant D.abs_resultant_le_l2norm_pow

/--
If the Hadamard/l2norm upper bound is strictly below the modular divisor, the
packaged bad-vector resultant data is contradictory.
-/
theorem no_badVector_of_l2norm_upper_lt_divisor
    (D : BadVectorResultantData)
    (hlt :
      (HexPolyZMathlib.l2norm D.f) ^ D.H.natDegree *
          (HexPolyZMathlib.l2norm D.H) ^ D.f.natDegree <
        (D.divisor : ℝ)) :
    False :=
  (not_lt_of_ge D.divisor_real_le_l2norm_pow) hlt

/--
Parameter-style wrapper for later callers that do not want to construct the
record explicitly in theorem statements.
-/
theorem badVector_resultant_bounds
    (f H : Polynomial ℤ) (p a d : Nat)
    (hp : 0 < p) (hd : 0 < d)
    (hcoprime :
      IsCoprime (f.map (Int.castRingHom ℚ)) (H.map (Int.castRingHom ℚ)))
    (hdiv : ((p ^ (a * d) : Nat) : ℤ) ∣ Polynomial.resultant f H) :
    (p ^ (a * d) : ℝ) ≤
      |((Polynomial.resultant f H : ℤ) : ℝ)| ∧
    |((Polynomial.resultant f H : ℤ) : ℝ)| ≤
      (HexPolyZMathlib.l2norm f) ^ H.natDegree *
        (HexPolyZMathlib.l2norm H) ^ f.natDegree := by
  let D : BadVectorResultantData :=
    { f := f
      H := H
      p := p
      a := a
      d := d
      p_pos := hp
      d_pos := hd
      coprime_over_rat := hcoprime
      resultant_divisible := hdiv }
  exact ⟨by simpa [D, divisor, resultant] using D.divisor_real_le_abs_resultant,
    by simpa [D, resultant] using D.abs_resultant_le_l2norm_pow⟩

/--
Parameter-style contradiction wrapper for callers that have the raw bad-vector
resultant hypotheses rather than a `BadVectorResultantData` record.
-/
theorem no_badVector_of_l2norm_upper_lt_divisor_params
    (f H : Polynomial ℤ) (p a d : Nat)
    (hp : 0 < p) (hd : 0 < d)
    (hcoprime :
      IsCoprime (f.map (Int.castRingHom ℚ)) (H.map (Int.castRingHom ℚ)))
    (hdiv : ((p ^ (a * d) : Nat) : ℤ) ∣ Polynomial.resultant f H)
    (hlt :
      (HexPolyZMathlib.l2norm f) ^ H.natDegree *
          (HexPolyZMathlib.l2norm H) ^ f.natDegree <
        (p ^ (a * d) : ℝ)) :
    False := by
  let D : BadVectorResultantData :=
    { f := f
      H := H
      p := p
      a := a
      d := d
      p_pos := hp
      d_pos := hd
      coprime_over_rat := hcoprime
      resultant_divisible := hdiv }
  exact D.no_badVector_of_l2norm_upper_lt_divisor (by
    simpa [D, divisor] using hlt)

end BadVectorResultantData

/--
Proof-facing witness tying an executable BHKS bad vector back to the abstract
integer-resultant data used by the termination proof.

The executable fields name the original `ZPoly`, the Hensel lift data, the
all-coefficients CLD lattice, the projected `L'` rows, and the selected local
factor index/degree.  The auxiliary polynomial is stored as a `Hex.ZPoly`; the
Mathlib-facing polynomial used in resultants is `auxiliaryPolynomial`.
-/
structure ExecutableBadVectorWitness where
  input : Hex.ZPoly
  liftData : Hex.LiftData
  lattice : Hex.BhksLatticeBasis
  projectedRows : Hex.BhksProjectedRows
  localFactorIndex : Nat
  localFactorDegree : Nat
  H : Hex.ZPoly
  lattice_matches_lift :
    lattice =
      Hex.bhksLatticeBasis input liftData.p liftData.k liftData.liftedFactors
  projected_factor_count :
    projectedRows.factorCount = lattice.factorCount

namespace ExecutableBadVectorWitness

/-- The input polynomial transported to Mathlib's `Polynomial ℤ`. -/
def inputPolynomial (W : ExecutableBadVectorWitness) : Polynomial ℤ :=
  HexPolyZMathlib.toPolynomial W.input

/-- The auxiliary bad-vector polynomial transported to Mathlib's `Polynomial ℤ`. -/
def auxiliaryPolynomial (W : ExecutableBadVectorWitness) : Polynomial ℤ :=
  HexPolyZMathlib.toPolynomial W.H

/-- The selected lifted factor, if the executable array contains the index. -/
def selectedLiftedFactor (W : ExecutableBadVectorWitness) : Hex.ZPoly :=
  W.liftData.liftedFactors.getD W.localFactorIndex 0

/--
Package an executable bad-vector witness and the remaining BHKS local
coprimality/divisibility hypotheses as abstract resultant data.
-/
def toResultantData
    (W : ExecutableBadVectorWitness)
    (hp : 0 < W.liftData.p)
    (hd : 0 < W.localFactorDegree)
    (hcoprime :
      IsCoprime
        ((W.inputPolynomial).map (Int.castRingHom ℚ))
        ((W.auxiliaryPolynomial).map (Int.castRingHom ℚ)))
    (hdiv :
      ((W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : Nat) : ℤ) ∣
        Polynomial.resultant W.inputPolynomial W.auxiliaryPolynomial) :
    BadVectorResultantData where
  f := W.inputPolynomial
  H := W.auxiliaryPolynomial
  p := W.liftData.p
  a := W.liftData.k
  d := W.localFactorDegree
  p_pos := hp
  d_pos := hd
  coprime_over_rat := hcoprime
  resultant_divisible := hdiv

/--
Executable bad-vector packaging theorem: once later BHKS work supplies the
local coprimality and modular-divisibility hypotheses, the existing resultant
lower/upper-bound theorem applies to the transported executable data.
-/
theorem badVector_resultant_bounds
    (W : ExecutableBadVectorWitness)
    (hp : 0 < W.liftData.p)
    (hd : 0 < W.localFactorDegree)
    (hcoprime :
      IsCoprime
        ((W.inputPolynomial).map (Int.castRingHom ℚ))
        ((W.auxiliaryPolynomial).map (Int.castRingHom ℚ)))
    (hdiv :
      ((W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : Nat) : ℤ) ∣
        Polynomial.resultant W.inputPolynomial W.auxiliaryPolynomial) :
    (W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : ℝ) ≤
      |((Polynomial.resultant W.inputPolynomial W.auxiliaryPolynomial : ℤ) : ℝ)| ∧
    |((Polynomial.resultant W.inputPolynomial W.auxiliaryPolynomial : ℤ) : ℝ)| ≤
      (HexPolyZMathlib.l2norm W.inputPolynomial) ^ W.auxiliaryPolynomial.natDegree *
        (HexPolyZMathlib.l2norm W.auxiliaryPolynomial) ^ W.inputPolynomial.natDegree := by
  simpa [inputPolynomial, auxiliaryPolynomial] using
    BadVectorResultantData.badVector_resultant_bounds
      W.inputPolynomial W.auxiliaryPolynomial
      W.liftData.p W.liftData.k W.localFactorDegree
      hp hd hcoprime hdiv

/--
Executable bad-vector contradiction wrapper: the transported witness cannot
exist when its Hadamard/l2norm upper bound is already below the modular divisor.
-/
theorem no_badVector_of_l2norm_upper_lt_divisor
    (W : ExecutableBadVectorWitness)
    (hp : 0 < W.liftData.p)
    (hd : 0 < W.localFactorDegree)
    (hcoprime :
      IsCoprime
        ((W.inputPolynomial).map (Int.castRingHom ℚ))
        ((W.auxiliaryPolynomial).map (Int.castRingHom ℚ)))
    (hdiv :
      ((W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : Nat) : ℤ) ∣
        Polynomial.resultant W.inputPolynomial W.auxiliaryPolynomial)
    (hlt :
      (HexPolyZMathlib.l2norm W.inputPolynomial) ^ W.auxiliaryPolynomial.natDegree *
          (HexPolyZMathlib.l2norm W.auxiliaryPolynomial) ^ W.inputPolynomial.natDegree <
        (W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : ℝ)) :
    False := by
  simpa [inputPolynomial, auxiliaryPolynomial] using
    BadVectorResultantData.no_badVector_of_l2norm_upper_lt_divisor_params
      W.inputPolynomial W.auxiliaryPolynomial
      W.liftData.p W.liftData.k W.localFactorDegree
      hp hd hcoprime hdiv hlt

end ExecutableBadVectorWitness

namespace BHKS

/--
The BHKS auxiliary polynomial `H_v` associated to an integer vector `v` over
the lifted local factors.

The construction follows the BHKS Lemma 3.2 recipe: each lifted factor `g_i`
contributes its centred-cut CLD coefficient array, scaled by `v_i`; the
results are summed coordinate-wise to produce a `Hex.ZPoly` of degree at most
`deg(input) - 1`.
-/
def auxiliaryPolynomial
    (input : Hex.ZPoly) (liftData : Hex.LiftData) (vec : Array Int) : Hex.ZPoly :=
  let n := input.degree?.getD 0
  let r := liftData.liftedFactors.size
  let coeffs : List Int := (List.range n).map fun j =>
    (List.range r).foldl (fun acc i =>
      acc +
        vec.getD i 0 *
          (Hex.cldCoeffs input liftData.p liftData.k
              (liftData.liftedFactors.getD i 0)).getD j 0) 0
  Hex.DensePoly.ofCoeffs coeffs.toArray

end BHKS

namespace ExecutableBadVectorWitness

/-- Promote an executable `Array Int` row to a vector function indexed by the
witness's projected factor count. -/
def projectedVectorFn (W : ExecutableBadVectorWitness) (vec : Array Int) :
    Fin W.projectedRows.factorCount → ℤ :=
  fun i => vec.getD i.val 0

/-- Store a proof-facing projected vector in the executable array shape used
by the BHKS auxiliary-polynomial construction. -/
def projectedVectorArray (W : ExecutableBadVectorWitness)
    (v : Fin W.projectedRows.factorCount → ℤ) : Array Int :=
  (List.ofFn v).toArray

/--
Canonical executable bad-vector witness for a fixed projected vector.

The auxiliary polynomial field is computed by the same BHKS construction used
in the executable CLD layer, and the selected local-factor degree is read from
the selected lifted factor.  This constructor discharges the structural part of
the BHKS bad-vector setup; the rational coprimality and resultant divisibility
clauses remain the genuine BHKS Lemma 3.2 algebraic obligations.
-/
def ofProjectedVector
    (input : Hex.ZPoly) (liftData : Hex.LiftData)
    (hrows :
      1 ≤
        (Hex.bhksLatticeBasis input liftData.p liftData.k
            liftData.liftedFactors).factorCount +
          (Hex.bhksLatticeBasis input liftData.p liftData.k
            liftData.liftedFactors).coeffWidth)
    (localFactorIndex : Nat)
    (v :
      Fin (Hex.bhksProjectedRows
        (Hex.bhksLatticeBasis input liftData.p liftData.k
          liftData.liftedFactors) hrows).factorCount → ℤ) :
    ExecutableBadVectorWitness where
  input := input
  liftData := liftData
  lattice := Hex.bhksLatticeBasis input liftData.p liftData.k liftData.liftedFactors
  projectedRows :=
    Hex.bhksProjectedRows
      (Hex.bhksLatticeBasis input liftData.p liftData.k liftData.liftedFactors)
      hrows
  localFactorIndex := localFactorIndex
  localFactorDegree :=
    (liftData.liftedFactors.getD localFactorIndex 0).degree?.getD 0
  H := BHKS.auxiliaryPolynomial input liftData (List.ofFn v).toArray
  lattice_matches_lift := rfl
  projected_factor_count := rfl

/-- `projectedVectorArray` is the canonical array representative of a
proof-facing projected vector. -/
theorem projectedVectorFn_projectedVectorArray
    (W : ExecutableBadVectorWitness)
    (v : Fin W.projectedRows.factorCount → ℤ) :
    W.projectedVectorFn (W.projectedVectorArray v) = v := by
  funext i
  simp [projectedVectorFn, projectedVectorArray]

/--
Bad-vector evidence for an executable BHKS bad-vector witness.

The witness's auxiliary polynomial `H` is the canonical BHKS auxiliary
polynomial of `bhksVector`, and the same vector lies in the projected integer
row span `L'` but not in the true-factor indicator lattice `W`.

This is the proof-facing package of the local BHKS Lemma 3.2 hypotheses used
by the resultant comparison.  Later construction work must prove these fields
from the executable CLD/Hensel data attached to an actual failed recovery run.
-/
structure IsBhksBadVectorSetup (W : ExecutableBadVectorWitness) where
  bhksVector : Array Int
  trueSupports : Set (Set (Fin W.projectedRows.factorCount))
  H_eq :
    W.H = BHKS.auxiliaryPolynomial W.input W.liftData bhksVector
  in_projected :
    W.projectedVectorFn bhksVector ∈ BHKS.projectedRowSpanInt W.projectedRows
  not_in_indicators :
    W.projectedVectorFn bhksVector ∉
      BHKS.trueFactorIndicatorLattice trueSupports
  localFactorDegree_pos : 0 < W.localFactorDegree
  coprime_input_aux_over_rat :
    IsCoprime
      (W.inputPolynomial.map (Int.castRingHom ℚ))
      (W.auxiliaryPolynomial.map (Int.castRingHom ℚ))
  resultant_divisible_by_p_pow :
    ((W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : Nat) : ℤ) ∣
      Polynomial.resultant W.inputPolynomial W.auxiliaryPolynomial

/--
Construct the BHKS bad-vector setup from the projected vector shape used by
cap separation.  The structural `L' \ W` fields are transported through the
canonical executable array representation; the local BHKS Lemma 3.2 algebraic
clauses remain explicit hypotheses.
-/
def isBhksBadVectorSetup_of_projected_not_indicator
    (W : ExecutableBadVectorWitness)
    (trueSupports : Set (Set (Fin W.projectedRows.factorCount)))
    (v : Fin W.projectedRows.factorCount → ℤ)
    (hH :
      W.H =
        BHKS.auxiliaryPolynomial W.input W.liftData
          (W.projectedVectorArray v))
    (hin : v ∈ BHKS.projectedRowSpanInt W.projectedRows)
    (hnot : v ∉ BHKS.trueFactorIndicatorLattice trueSupports)
    (hd : 0 < W.localFactorDegree)
    (hcoprime :
      IsCoprime
        (W.inputPolynomial.map (Int.castRingHom ℚ))
        (W.auxiliaryPolynomial.map (Int.castRingHom ℚ)))
    (hdiv :
      ((W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : Nat) : ℤ) ∣
        Polynomial.resultant W.inputPolynomial W.auxiliaryPolynomial) :
    IsBhksBadVectorSetup W := by
  refine
    { bhksVector := W.projectedVectorArray v
      trueSupports := trueSupports
      H_eq := hH
      in_projected := ?_
      not_in_indicators := ?_
      localFactorDegree_pos := hd
      coprime_input_aux_over_rat := hcoprime
      resultant_divisible_by_p_pow := hdiv }
  · simpa [projectedVectorFn_projectedVectorArray] using hin
  · simpa [projectedVectorFn_projectedVectorArray] using hnot

/--
Concrete fixed-vector bad-vector setup constructor.

For a projected vector `v ∈ L' \ W`, the witness built by
`ofProjectedVector` has the canonical auxiliary polynomial by construction and
uses the executable selected local-factor degree.  Callers still provide the
positive-degree fact and the two resultant hypotheses; this is the intended
boundary before the full BHKS Lemma 3.2 proof.
-/
def isBhksBadVectorSetup_of_projectedVector
    (input : Hex.ZPoly) (liftData : Hex.LiftData)
    (hrows :
      1 ≤
        (Hex.bhksLatticeBasis input liftData.p liftData.k
            liftData.liftedFactors).factorCount +
          (Hex.bhksLatticeBasis input liftData.p liftData.k
            liftData.liftedFactors).coeffWidth)
    (localFactorIndex : Nat)
    (v :
      Fin (Hex.bhksProjectedRows
        (Hex.bhksLatticeBasis input liftData.p liftData.k
          liftData.liftedFactors) hrows).factorCount → ℤ)
    (trueSupports :
      Set (Set (Fin (Hex.bhksProjectedRows
        (Hex.bhksLatticeBasis input liftData.p liftData.k
          liftData.liftedFactors) hrows).factorCount)))
    (hin :
      v ∈ BHKS.projectedRowSpanInt
        (Hex.bhksProjectedRows
          (Hex.bhksLatticeBasis input liftData.p liftData.k
            liftData.liftedFactors) hrows))
    (hnot :
      v ∉ BHKS.trueFactorIndicatorLattice trueSupports)
    (hdegree :
      0 < (liftData.liftedFactors.getD localFactorIndex 0).degree?.getD 0)
    (hcoprime :
      IsCoprime
        ((ofProjectedVector input liftData hrows localFactorIndex v).inputPolynomial.map
          (Int.castRingHom ℚ))
        ((ofProjectedVector input liftData hrows localFactorIndex v).auxiliaryPolynomial.map
          (Int.castRingHom ℚ)))
    (hdiv :
      (((ofProjectedVector input liftData hrows localFactorIndex v).liftData.p ^
          ((ofProjectedVector input liftData hrows localFactorIndex v).liftData.k *
            (ofProjectedVector input liftData hrows localFactorIndex v).localFactorDegree) :
          Nat) : ℤ) ∣
        Polynomial.resultant
          (ofProjectedVector input liftData hrows localFactorIndex v).inputPolynomial
          (ofProjectedVector input liftData hrows localFactorIndex v).auxiliaryPolynomial) :
    IsBhksBadVectorSetup
      (ofProjectedVector input liftData hrows localFactorIndex v) := by
  let W := ofProjectedVector input liftData hrows localFactorIndex v
  exact
    isBhksBadVectorSetup_of_projected_not_indicator
      W trueSupports v
      (by
        simp [W, ofProjectedVector, projectedVectorArray])
      hin hnot
      (by
        simpa [W, ofProjectedVector] using hdegree)
      hcoprime hdiv

/--
Per-vector algebraic bridge needed to turn a projected vector in `L' \ W` into
the exact bad-vector setup callback consumed by cap separation.

The structural `L' \ W` facts are supplied by the callback arguments.  This
record packages the remaining BHKS Lemma 3.2 data: the canonical auxiliary
polynomial attached to the projected vector, positivity of the selected local
factor degree, rational coprimality, and the `p^(k*d)` resultant divisibility.

Only `auxiliary_eq` depends on the projected vector; the other three fields
are properties of the fixed witness data (`W.H`, `W.input`, `W.liftData`) and
are not quantified over `v`.
-/
structure ProjectedBadVectorSetupBridge
    (W : ExecutableBadVectorWitness)
    (trueSupports : Set (Set (Fin W.projectedRows.factorCount))) where
  auxiliary_eq :
    ∀ v : Fin W.projectedRows.factorCount → ℤ,
      v ∈ BHKS.projectedRowSpanInt W.projectedRows →
        v ∉ BHKS.trueFactorIndicatorLattice trueSupports →
          W.H =
            BHKS.auxiliaryPolynomial W.input W.liftData
              (W.projectedVectorArray v)
  localFactorDegree_pos : 0 < W.localFactorDegree
  coprime_input_aux_over_rat :
    IsCoprime
      (W.inputPolynomial.map (Int.castRingHom ℚ))
      (W.auxiliaryPolynomial.map (Int.castRingHom ℚ))
  resultant_divisible_by_p_pow :
    ((W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : Nat) : ℤ) ∣
      Polynomial.resultant W.inputPolynomial W.auxiliaryPolynomial

/--
Convert the packaged projected-vector bridge into the callback shape expected
by `BHKS.ExecutableCapSeparationHypotheses`.
-/
def bad_setup_of_projected_not_indicator
    (W : ExecutableBadVectorWitness)
    (trueSupports : Set (Set (Fin W.projectedRows.factorCount)))
    (hbridge : ProjectedBadVectorSetupBridge W trueSupports) :
    ∀ v : Fin W.projectedRows.factorCount → ℤ,
      v ∈ BHKS.projectedRowSpanInt W.projectedRows →
        v ∉ BHKS.trueFactorIndicatorLattice trueSupports →
          IsBhksBadVectorSetup W := by
  intro v hin hnot
  exact
    isBhksBadVectorSetup_of_projected_not_indicator
      W trueSupports v
      (hbridge.auxiliary_eq v hin hnot)
      hin hnot
      hbridge.localFactorDegree_pos
      hbridge.coprime_input_aux_over_rat
      hbridge.resultant_divisible_by_p_pow

/-- BHKS Lemma 3.2: the selected local-factor degree is positive whenever the
witness carries a bad-vector setup. -/
theorem localFactorDegree_pos_of_bhks_bad
    (W : ExecutableBadVectorWitness) (h_bad : IsBhksBadVectorSetup W) :
    0 < W.localFactorDegree := by
  exact h_bad.localFactorDegree_pos

/--
BHKS Lemma 3.2 (rational coprimality clause): the input and auxiliary
polynomials are coprime over `ℚ` whenever the witness carries a bad-vector
setup.
-/
theorem coprime_input_aux_over_rat_of_bhks_bad
    (W : ExecutableBadVectorWitness) (h_bad : IsBhksBadVectorSetup W) :
    IsCoprime
      (W.inputPolynomial.map (Int.castRingHom ℚ))
      (W.auxiliaryPolynomial.map (Int.castRingHom ℚ)) := by
  exact h_bad.coprime_input_aux_over_rat

/--
BHKS Lemma 3.2 (modular divisibility clause): the integer resultant of the
input and auxiliary polynomials is divisible by `p^(k * d)` whenever the
witness carries a bad-vector setup, where `p` is the BHKS prime, `k` is the
lift precision, and `d` is the selected local-factor degree.
-/
theorem resultant_divisible_by_p_pow_of_bhks_bad
    (W : ExecutableBadVectorWitness) (h_bad : IsBhksBadVectorSetup W) :
    ((W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : Nat) : ℤ) ∣
      Polynomial.resultant W.inputPolynomial W.auxiliaryPolynomial := by
  exact h_bad.resultant_divisible_by_p_pow

/--
Package a BHKS bad-vector setup as the abstract resultant data consumed by
the lower/upper-bound comparison lemmas.
-/
def resultantDataOfBhksBad
    (W : ExecutableBadVectorWitness) (h_bad : IsBhksBadVectorSetup W)
    (hp : 0 < W.liftData.p) :
    BadVectorResultantData :=
  W.toResultantData
    hp
    (localFactorDegree_pos_of_bhks_bad W h_bad)
    (coprime_input_aux_over_rat_of_bhks_bad W h_bad)
    (resultant_divisible_by_p_pow_of_bhks_bad W h_bad)

/--
BHKS Lemma 3.2 bound package: a bad-vector setup gives both the modular
resultant lower bound and the Hadamard/l2norm upper bound without callers
projecting the setup fields manually.
-/
theorem badVector_resultant_bounds_of_bhks_bad
    (W : ExecutableBadVectorWitness)
    (h_bad : IsBhksBadVectorSetup W)
    (hp : 0 < W.liftData.p) :
    (W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : ℝ) ≤
      |((Polynomial.resultant W.inputPolynomial W.auxiliaryPolynomial : ℤ) : ℝ)| ∧
    |((Polynomial.resultant W.inputPolynomial W.auxiliaryPolynomial : ℤ) : ℝ)| ≤
      (HexPolyZMathlib.l2norm W.inputPolynomial) ^ W.auxiliaryPolynomial.natDegree *
        (HexPolyZMathlib.l2norm W.auxiliaryPolynomial) ^ W.inputPolynomial.natDegree :=
  W.badVector_resultant_bounds
    hp
    (localFactorDegree_pos_of_bhks_bad W h_bad)
    (coprime_input_aux_over_rat_of_bhks_bad W h_bad)
    (resultant_divisible_by_p_pow_of_bhks_bad W h_bad)

/--
Combined BHKS Lemma 3.2 contradiction: an executable bad-vector witness whose
`H` field is the canonical BHKS auxiliary polynomial of a vector in `L' \ W`
cannot exist once the Hadamard/l2norm upper bound on the integer resultant of
the input and the auxiliary polynomial drops below the modular divisor
`p^(k * d)`.

The selected-degree positivity, rational coprimality, and resultant
divisibility are discharged by `localFactorDegree_pos_of_bhks_bad`,
`coprime_input_aux_over_rat_of_bhks_bad`, and
`resultant_divisible_by_p_pow_of_bhks_bad`; this theorem chains them through
the existing executable bad-vector contradiction
`ExecutableBadVectorWitness.no_badVector_of_l2norm_upper_lt_divisor`.
-/
theorem no_bhks_bad_setup_of_l2norm_upper_lt_divisor
    (W : ExecutableBadVectorWitness)
    (h_bad : IsBhksBadVectorSetup W)
    (hp : 0 < W.liftData.p)
    (hlt :
      (HexPolyZMathlib.l2norm W.inputPolynomial) ^
          W.auxiliaryPolynomial.natDegree *
        (HexPolyZMathlib.l2norm W.auxiliaryPolynomial) ^
          W.inputPolynomial.natDegree <
      (W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : ℝ)) :
    False :=
  W.no_badVector_of_l2norm_upper_lt_divisor
    hp
    (localFactorDegree_pos_of_bhks_bad W h_bad)
    (coprime_input_aux_over_rat_of_bhks_bad W h_bad)
    (resultant_divisible_by_p_pow_of_bhks_bad W h_bad)
    hlt

end ExecutableBadVectorWitness

end

end HexBerlekampZassenhausMathlib
