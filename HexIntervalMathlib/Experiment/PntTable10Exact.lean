/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.PntTable10Convex
public import HexIntervalMathlib.Experiment.PntTable10Pointwise
public import HexIntervalMathlib.Experiment.PntTable10LargePointwise
public import HexIntervalMathlib.Experiment.PntTable10LogCoupled

@[expose] public section

/-!
# Exact-supremum bridge for PNT+ BKLNW Table 10

This module copies only the mathematical shape of PNT+'s `B_8_exact`, with
the three source coefficients explicit.  It connects the bounded,
source-authenticated numerical providers to the exact interval supremum used
by PNT+'s unchanged Table 10 dispatcher.  PNT+ can identify this definition
with `B_8_exact` after unfolding `B_8_exact` and `B`; Hex neither imports nor
reimplements the surrounding PNT development.
-/

namespace Hex.Interval.Experiment.PntTable10Exact

open Real Set Finset

/-- PNT+'s exact Lemma-8 supremum with its three row coefficients exposed.
After unfolding PNT+'s `B_8_exact` and `B`, this is definitionally the same
expression with `a1 = Inputs.default.a₁ b`,
`a2 = Inputs.default.a₂ b`, and `epsilon = Inputs.default.ε b`. -/
noncomputable def exactBound (k : Nat) (a1 a2 epsilon b b' : Real) : Real :=
  iSup (ι := Set.Icc (Real.exp b) (Real.exp b')) fun x =>
    a1 * (Real.log x) ^ k * x ^ (-(1 : Real) / 2) +
      a2 * (Real.log x) ^ k * x ^ (-(2 : Real) / 3) +
        epsilon * (Real.log x) ^ k

/-- Expansion matching PNT+'s `B_8_exact` after unfolding its two-term
coefficient function.  This pins the localized rewrite to the source
definition rather than merely to a numerically similar majorant. -/
theorem exactBound_eq_sourceSum (k : Nat) (a1 a2 epsilon b b' : Real) :
    exactBound k a1 a2 epsilon b b' =
      iSup (ι := Set.Icc (Real.exp b) (Real.exp b')) fun x =>
        (∑ ell ∈ Finset.Icc (1 : Nat) 2,
          (if ell = 1 then a1 else if ell = 2 then a2 else 0) *
            (Real.log x) ^ k *
              x ^ (-(ell : Real) / ((ell : Real) + 1))) +
          epsilon * (Real.log x) ^ k := by
  unfold exactBound
  congr 1
  funext x
  rw [show Finset.Icc (1 : Nat) 2 = {1, 2} by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num

/-- A full logarithmic-interval majorant bounds the exact supremum.  The
coefficient hypotheses are the three non-numerical PNT+ row facts retained by
the localized rewrite. -/
theorem exactBound_le_of_majorant (k : Nat) (a1 a2 epsilon A1 A2 E b b' T : Real)
    (hbb' : b ≤ b') (hb0 : 0 ≤ b)
    (_hA1 : 0 ≤ A1) (_hA2 : 0 ≤ A2) (_hE : 0 ≤ E)
    (ha1 : a1 ≤ A1) (ha2 : a2 ≤ A2) (hepsilon : epsilon ≤ E)
    (hmajorant : ∀ y ∈ Set.Icc b b',
      A1 * y ^ k * Real.exp (-(y / 2)) +
        A2 * y ^ k * Real.exp (-(2 * y / 3)) + E * y ^ k ≤ T) :
    exactBound k a1 a2 epsilon b b' ≤ T := by
  let interval : Set Real := Set.Icc (Real.exp b) (Real.exp b')
  haveI : Nonempty interval :=
    ⟨Real.exp b, by
      change Real.exp b ∈ Set.Icc (Real.exp b) (Real.exp b')
      exact ⟨le_rfl, Real.exp_le_exp.mpr hbb'⟩⟩
  unfold exactBound
  apply ciSup_le
  rintro ⟨x, hxLower, hxUpper⟩
  have xPositive : 0 < x := (Real.exp_pos b).trans_le hxLower
  have logMember : Real.log x ∈ Set.Icc b b' := by
    constructor
    · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos b) hxLower
    · simpa only [Real.log_exp] using Real.log_le_log xPositive hxUpper
  have logNonnegative : 0 ≤ Real.log x := by
    exact hb0.trans logMember.1
  have logPowerNonnegative : 0 ≤ (Real.log x) ^ k := pow_nonneg logNonnegative k
  have firstExp : x ^ (-(1 : Real) / 2) = Real.exp (-(Real.log x / 2)) := by
    rw [Real.rpow_def_of_pos xPositive]
    congr 1
    ring
  have secondExp : x ^ (-(2 : Real) / 3) =
      Real.exp (-(2 * Real.log x / 3)) := by
    rw [Real.rpow_def_of_pos xPositive]
    congr 1
    ring
  rw [firstExp, secondExp]
  have firstNonnegative :
      0 ≤ (Real.log x) ^ k * Real.exp (-(Real.log x / 2)) :=
    mul_nonneg logPowerNonnegative (Real.exp_pos _).le
  have secondNonnegative :
      0 ≤ (Real.log x) ^ k * Real.exp (-(2 * Real.log x / 3)) :=
    mul_nonneg logPowerNonnegative (Real.exp_pos _).le
  calc
    a1 * (Real.log x) ^ k * Real.exp (-(Real.log x / 2)) +
          a2 * (Real.log x) ^ k * Real.exp (-(2 * Real.log x / 3)) +
          epsilon * (Real.log x) ^ k
        ≤ A1 * (Real.log x) ^ k * Real.exp (-(Real.log x / 2)) +
          A2 * (Real.log x) ^ k * Real.exp (-(2 * Real.log x / 3)) +
          E * (Real.log x) ^ k := by
            gcongr
    _ ≤ T := hmajorant (Real.log x) logMember

/-- The one-point upper premise used by PNT+'s late-row reduction also bounds
the exact supremum.  This is the ordinary-kernel counterpart of
`row_bound_pointwise`; no numerical tactic or source table is hidden here. -/
theorem exactBound_le_of_pointwise (k : Nat) (a1 a2 epsilon A1 A2 E b b' T : Real)
    (hbb' : b ≤ b') (hb0 : 0 ≤ b)
    (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hE : 0 ≤ E)
    (ha1 : a1 ≤ A1) (ha2 : a2 ≤ A2) (hepsilon : epsilon ≤ E)
    (hpoint : A1 * b' ^ k * Real.exp (-(b / 2)) +
      A2 * b' ^ k * Real.exp (-(2 * b / 3)) + E * b' ^ k ≤ T) :
    exactBound k a1 a2 epsilon b b' ≤ T := by
  apply exactBound_le_of_majorant k a1 a2 epsilon A1 A2 E b b' T hbb'
    hb0 hA1 hA2 hE ha1 ha2 hepsilon
  intro y hy
  have hy0 : 0 ≤ y := hb0.trans hy.1
  have hb'0 : 0 ≤ b' := hy0.trans hy.2
  have powerLe : y ^ k ≤ b' ^ k := pow_le_pow_left₀ hy0 hy.2 k
  have firstExpLe : Real.exp (-(y / 2)) ≤ Real.exp (-(b / 2)) :=
    Real.exp_le_exp.mpr (by linarith [hy.1])
  have secondExpLe : Real.exp (-(2 * y / 3)) ≤ Real.exp (-(2 * b / 3)) :=
    Real.exp_le_exp.mpr (by linarith [hy.1])
  calc
    A1 * y ^ k * Real.exp (-(y / 2)) +
          A2 * y ^ k * Real.exp (-(2 * y / 3)) + E * y ^ k
        ≤ A1 * b' ^ k * Real.exp (-(b / 2)) +
          A2 * b' ^ k * Real.exp (-(2 * b / 3)) + E * b' ^ k := by
            gcongr
    _ ≤ T := hpoint

/-! ## Source-pinned adapters

Each adapter ends at the exact supremum while retaining the source tuple
membership, column membership, and the three PNT+-owned coefficient bounds.
The source project keeps its already-proved coefficient lemmas; only the
former numerical tactic premise is replaced by the authenticated Hex row
provider.
-/

namespace Shard

/-- Exact-supremum form of the five checked row-25 coordinates. -/
theorem row25OfMem (B : Nat → Real)
    (member : ((25 : Real), B 1, B 2, B 3, B 4, B 5) ∈
      PntTable10Shard.sourceTable)
    (k : Nat) (column : k ∈ Finset.Icc 1 5)
    (a1 a2 epsilon : Real)
    (hA1 : 0 ≤ PntTable10Shard.certificate.a1.value)
    (hA2 : 0 ≤ PntTable10Shard.certificate.a2.value)
    (hE : 0 ≤ PntTable10Shard.certificate.epsilon.value)
    (ha1 : a1 ≤ PntTable10Shard.certificate.a1.value)
    (ha2 : a2 ≤ PntTable10Shard.certificate.a2.value)
    (hepsilon : epsilon ≤ PntTable10Shard.certificate.epsilon.value) :
    exactBound k a1 a2 epsilon 25 26 ≤
      B k * PntTable10Shard.margin.value := by
  apply exactBound_le_of_majorant k a1 a2 epsilon
    PntTable10Shard.certificate.a1.value
    PntTable10Shard.certificate.a2.value
    PntTable10Shard.certificate.epsilon.value 25 26
    (B k * PntTable10Shard.margin.value)
    (by norm_num) (by norm_num) hA1 hA2 hE
    ha1 ha2 hepsilon
  simpa only [PntTable10Shard.majorant, PntTable10Shard.coefficientMajorant] using
    PntTable10Shard.row25OfMem B member k column

end Shard

namespace Convex

/-- Exact-supremum form of every checked coordinate in rows 60--85. -/
theorem rowOfMem (value : PntTable10Convex.RowCertificate)
    (rowMember : value ∈ PntTable10Convex.rows) (B : Nat → Real)
    (member : ((value.row : Real), B 1, B 2, B 3, B 4, B 5) ∈
      PntTable10Convex.sourceTable)
    (k : Nat) (column : k ∈ Finset.Icc 1 5)
    (a1 a2 epsilon : Real)
    (hbb' : (value.row : Real) ≤ value.nextRow)
    (hb0 : (0 : Real) ≤ value.row)
    (hA1 : 0 ≤ PntTable10Convex.a1.value)
    (hA2 : 0 ≤ value.a2.value) (hE : 0 ≤ value.epsilon.value)
    (ha1 : a1 ≤ PntTable10Convex.a1.value)
    (ha2 : a2 ≤ value.a2.value)
    (hepsilon : epsilon ≤ value.epsilon.value) :
    exactBound k a1 a2 epsilon value.row value.nextRow ≤
      B k * PntTable10Shard.margin.value := by
  apply exactBound_le_of_majorant k a1 a2 epsilon
    PntTable10Convex.a1.value value.a2.value value.epsilon.value
    value.row value.nextRow (B k * PntTable10Shard.margin.value)
    hbb' hb0 hA1 hA2 hE ha1 ha2 hepsilon
  simpa only [PntTable10Convex.majorant,
    PntTable10Shard.coefficientMajorant] using
      PntTable10Convex.rowOfMem value rowMember B member k column

end Convex

namespace Pointwise

/-- Exact-supremum form of every checked coordinate in rows 90 and 95. -/
theorem rowOfMem (value : PntTable10Pointwise.RowCertificate)
    (rowMember : value ∈ PntTable10Pointwise.rows) (B : Nat → Real)
    (member : ((value.row : Real), B 1, B 2, B 3, B 4, B 5) ∈
      PntTable10Pointwise.sourceTable)
    (k : Nat) (column : k ∈ Finset.Icc 1 5)
    (a1 a2 epsilon : Real)
    (hbb' : (value.row : Real) ≤ value.nextRow)
    (hb0 : (0 : Real) ≤ value.row)
    (hA1 : 0 ≤ value.a1.value) (hA2 : 0 ≤ value.a2.value)
    (hE : 0 ≤ value.epsilon.value)
    (ha1 : a1 ≤ value.a1.value) (ha2 : a2 ≤ value.a2.value)
    (hepsilon : epsilon ≤ value.epsilon.value) :
    exactBound k a1 a2 epsilon value.row value.nextRow ≤
      B k * PntTable10Shard.margin.value := by
  apply exactBound_le_of_pointwise k a1 a2 epsilon value.a1.value
    value.a2.value value.epsilon.value value.row value.nextRow
    (B k * PntTable10Shard.margin.value)
    hbb' hb0 hA1 hA2 hE ha1 ha2 hepsilon
  have source := PntTable10Pointwise.rowOfMem value rowMember B member k column
  unfold PntTable10Pointwise.premise at source
  simpa only [div_eq_mul_inv, one_div, one_mul, mul_comm, mul_left_comm, mul_assoc]
    using source

end Pointwise

namespace LargePointwise

/-- Exact-supremum form of the five checked row-13800.7464 coordinates. -/
theorem rowOfMem (B : Nat → Real)
    (member : (PntTable10LargePointwise.certificate.row.value,
      B 1, B 2, B 3, B 4, B 5) ∈ PntTable10LargePointwise.sourceTable)
    (k : Nat) (column : k ∈ Finset.Icc 1 5)
    (a1 a2 epsilon : Real)
    (hbb' : PntTable10LargePointwise.certificate.row.value ≤
      (PntTable10LargePointwise.certificate.nextRow : Real))
    (hb0 : 0 ≤ PntTable10LargePointwise.certificate.row.value)
    (hA1 : 0 ≤ PntTable10LargePointwise.certificate.a1.value)
    (hA2 : 0 ≤ PntTable10LargePointwise.certificate.a2.value)
    (hE : 0 ≤ PntTable10LargePointwise.certificate.epsilon.value)
    (ha1 : a1 ≤ PntTable10LargePointwise.certificate.a1.value)
    (ha2 : a2 ≤ PntTable10LargePointwise.certificate.a2.value)
    (hepsilon : epsilon ≤
      PntTable10LargePointwise.certificate.epsilon.value) :
    exactBound k a1 a2 epsilon
        PntTable10LargePointwise.certificate.row.value
        PntTable10LargePointwise.certificate.nextRow ≤
      B k * PntTable10Shard.margin.value := by
  apply exactBound_le_of_pointwise k a1 a2 epsilon
    PntTable10LargePointwise.certificate.a1.value
    PntTable10LargePointwise.certificate.a2.value
    PntTable10LargePointwise.certificate.epsilon.value
    PntTable10LargePointwise.certificate.row.value
    PntTable10LargePointwise.certificate.nextRow
    (B k * PntTable10Shard.margin.value)
    hbb' hb0 hA1 hA2 hE ha1 ha2 hepsilon
  have source := PntTable10LargePointwise.rowOfMem B member k column
  unfold PntTable10LargePointwise.premise at source
  simpa only [div_eq_mul_inv, one_div, one_mul, mul_comm, mul_left_comm, mul_assoc]
    using source

end LargePointwise

namespace LogCoupled

/-- Exact-supremum form of both checked logarithmic-transition rows. -/
theorem rowOfMem (value : PntTable10LogCoupled.RowCertificate)
    (rowMember : value ∈ PntTable10LogCoupled.rows
      PntTable10LogCoupled.certificate) (B : Nat → Real)
    (member : (PntTable10LogCoupled.lowerPoint value,
      B 1, B 2, B 3, B 4, B 5) ∈ PntTable10LogCoupled.sourceTable)
    (k : Nat) (column : k ∈ Finset.Icc 1 5)
    (a1 a2 epsilon : Real)
    (hbb' : PntTable10LogCoupled.lowerPoint value ≤
      PntTable10LogCoupled.upperPoint value)
    (hb0 : 0 ≤ PntTable10LogCoupled.lowerPoint value)
    (hA1 : 0 ≤ value.a1.value) (hA2 : 0 ≤ value.a2.value)
    (hE : 0 ≤ value.epsilon.value)
    (ha1 : a1 ≤ value.a1.value) (ha2 : a2 ≤ value.a2.value)
    (hepsilon : epsilon ≤ value.epsilon.value) :
    exactBound k a1 a2 epsilon
        (PntTable10LogCoupled.lowerPoint value)
        (PntTable10LogCoupled.upperPoint value) ≤
      B k * PntTable10Shard.margin.value := by
  apply exactBound_le_of_majorant k a1 a2 epsilon value.a1.value
    value.a2.value value.epsilon.value
    (PntTable10LogCoupled.lowerPoint value)
    (PntTable10LogCoupled.upperPoint value)
    (B k * PntTable10Shard.margin.value)
    hbb' hb0 hA1 hA2 hE ha1 ha2 hepsilon
  simpa only [PntTable10LogCoupled.majorant,
    PntTable10Shard.coefficientMajorant] using
      PntTable10LogCoupled.rowOfMem value rowMember B member k column

end LogCoupled

end Hex.Interval.Experiment.PntTable10Exact
