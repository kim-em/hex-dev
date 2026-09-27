/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealClosure.Element
public import HexPoly.Monic

public section

/-!
# Yun decomposition

The executable recurrence uses the ordinary dense-polynomial operations. The
raw version supports tower coefficients whose stored equality is not value
equality. The public version requires an ordered field, hence characteristic
zero. Their correctness theorems belong in the Mathlib companion.
-/

namespace Hex.RealClosure.Yun

universe u

attribute [local instance] Lean.Grind.Semiring.natCast

/-- Zero is kept separate from the scalar-times-factors result. -/
inductive Decomposition (K : Type u) [Zero K] [DecidableEq K] where
  | zero
  | factors (unit : K) (entries : Array (DensePoly K × Nat))

/-- The Yun recurrence. `v` contains factors whose multiplicity is at least
`multiplicity`; `w` is the derivative quotient carried between rounds. The
original degree bounds the fuel, including rounds that emit no factor. -/
@[expose] def loop {K : Type u} [Zero K] [One K] [Add K] [Sub K]
    [Mul K] [Div K] [Inv K] [NatCast K] [DecidableEq K]
    (v w : DensePoly K) (multiplicity fuel : Nat)
    (out : Array (DensePoly K × Nat)) : Array (DensePoly K × Nat) :=
  match fuel with
  | 0 => out
  | fuel + 1 =>
      if v.natDegree = 0 then out
      else
        let t := w - DensePoly.derivativeImpl v
        let z := DensePoly.monicize (DensePoly.gcd v t)
        let out := if 0 < z.natDegree then out.push (z, multiplicity) else out
        loop (v / z) (t / z) (multiplicity + 1) fuel out

/-- Run the recurrence on raw coefficients whose operations need not satisfy
field laws as literal equality. The companion must supply an interpretation
into an ordered field before claiming multiplicity correctness. -/
@[expose] def decomposeRaw {K : Type u} [Zero K] [One K] [Add K] [Sub K]
    [Mul K] [Div K] [Inv K] [NatCast K] [DecidableEq K]
    (f : DensePoly K) : Decomposition K :=
  if f.isZero then .zero
  else if f.natDegree = 0 then .factors f.leadingCoeff #[]
  else
    let a := DensePoly.monicize
      (DensePoly.gcd f (DensePoly.derivativeImpl f))
    let v := f / a
    let w := DensePoly.derivativeImpl f / a
    .factors f.leadingCoeff (loop v w 1 (f.natDegree + 1) #[])

@[simp] theorem decomposeRaw_zero {K : Type u} [Zero K] [One K]
    [Add K] [Sub K] [Mul K] [Div K] [Inv K] [NatCast K]
    [DecidableEq K] :
    decomposeRaw (0 : DensePoly K) = .zero := by
  have hz : DensePoly.isZero (0 : DensePoly K) = true := by rfl
  simp [decomposeRaw, hz]

theorem decomposeRaw_constant {K : Type u} [Zero K] [One K]
    [Add K] [Sub K] [Mul K] [Div K] [Inv K] [NatCast K]
    [DecidableEq K] (f : DensePoly K)
    (hzero : f.isZero = false) (hdegree : f.natDegree = 0) :
    decomposeRaw f = .factors f.leadingCoeff #[] := by
  simp [decomposeRaw, hzero, hdegree]

/-- Yun's recurrence over a lawful ordered field. Zero has its own result;
nonzero constants return their scalar and an empty factor list. -/
@[expose] def decompose {K : Type u} [Lean.Grind.Field K]
    [LE K] [LT K] [Std.IsPreorder K]
    [Lean.Grind.OrderedRing K] [DecidableEq K]
    (f : DensePoly K) : Decomposition K :=
  decomposeRaw f

/-- Reconstruct the polynomial denoted by a scalar and multiplicity factors.
This is also useful to independently check a computed result. -/
@[expose] def reconstruct {K : Type u} [Lean.Grind.CommRing K]
    [DecidableEq K] (unit : K)
    (entries : Array (DensePoly K × Nat)) : DensePoly K :=
  entries.foldl (fun product entry => product * entry.1 ^ entry.2)
    (DensePoly.C unit)

/-- Degree accounted for by the emitted factors. -/
@[expose] def degreeSum {K : Type u} [Zero K] [DecidableEq K]
    (entries : Array (DensePoly K × Nat)) : Nat :=
  entries.foldl (fun degree entry =>
    degree + entry.2 * entry.1.natDegree) 0

/-- Optional exact replay of a Yun result. The field and order hypotheses
exclude positive characteristic; this check is not run inside `decompose`. -/
@[expose] def check {K : Type u} [Lean.Grind.Field K]
    [LE K] [LT K] [Std.IsPreorder K]
    [Lean.Grind.OrderedRing K] [DecidableEq K]
    (f : DensePoly K) : Decomposition K → Bool
  | .zero => f.isZero
  | .factors unit entries =>
      !f.isZero && decide (unit ≠ 0) &&
      entries.all (fun entry =>
        0 < entry.2 && 0 < entry.1.natDegree &&
          decide (entry.1.leadingCoeff = 1) &&
          (DensePoly.gcd entry.1
            (DensePoly.derivativeImpl entry.1)).natDegree == 0) &&
      decide (entries.toList.Pairwise fun a b => a.2 < b.2) &&
      decide (entries.toList.Pairwise fun a b =>
        (DensePoly.gcd a.1 b.1).natDegree = 0) &&
      decide (reconstruct unit entries = f) &&
        decide (degreeSum entries = f.natDegree)

@[simp] theorem check_zero_iff {K : Type u} [Lean.Grind.Field K]
    [LE K] [LT K] [Std.IsPreorder K]
    [Lean.Grind.OrderedRing K] [DecidableEq K]
    (f : DensePoly K) : check f .zero = true ↔ f = 0 := by
  simp only [check, DensePoly.isZero_eq_true_iff,
    DensePoly.size_eq_zero_iff]

/-- A nonzero Yun result must carry a nonzero unit. -/
theorem check_unit {K : Type u} [Lean.Grind.Field K]
    [LE K] [LT K] [Std.IsPreorder K]
    [Lean.Grind.OrderedRing K] [DecidableEq K]
    (f : DensePoly K) (unit : K)
    (entries : Array (DensePoly K × Nat))
    (h : check f (.factors unit entries) = true) : unit ≠ 0 := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  grind

/-- Accepted replay reconstructs the input and accounts for its degree. -/
theorem check_reconstruct {K : Type u} [Lean.Grind.Field K]
    [LE K] [LT K] [Std.IsPreorder K]
    [Lean.Grind.OrderedRing K] [DecidableEq K]
    (f : DensePoly K) (unit : K)
    (entries : Array (DensePoly K × Nat))
    (h : check f (.factors unit entries) = true) :
    reconstruct unit entries = f ∧
      degreeSum entries = f.natDegree := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  grind

/-- Replay requires strictly increasing multiplicity labels. -/
theorem check_multiplicities {K : Type u} [Lean.Grind.Field K]
    [LE K] [LT K] [Std.IsPreorder K]
    [Lean.Grind.OrderedRing K] [DecidableEq K]
    (f : DensePoly K) (unit : K)
    (entries : Array (DensePoly K × Nat))
    (h : check f (.factors unit entries) = true) :
    entries.toList.Pairwise (fun a b => a.2 < b.2) := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  grind

/-- Replay requires every pair of emitted factors to have constant gcd. -/
theorem check_coprime {K : Type u} [Lean.Grind.Field K]
    [LE K] [LT K] [Std.IsPreorder K]
    [Lean.Grind.OrderedRing K] [DecidableEq K]
    (f : DensePoly K) (unit : K)
    (entries : Array (DensePoly K × Nat))
    (h : check f (.factors unit entries) = true) :
    entries.toList.Pairwise (fun a b =>
      (DensePoly.gcd a.1 b.1).natDegree = 0) := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  grind

/-- Replay checks each factor's degree, monicity, and squarefree gcd. -/
theorem check_factor {K : Type u} [Lean.Grind.Field K]
    [LE K] [LT K] [Std.IsPreorder K]
    [Lean.Grind.OrderedRing K] [DecidableEq K]
    (f : DensePoly K) (unit : K)
    (entries : Array (DensePoly K × Nat))
    (entry : DensePoly K × Nat) (hmem : entry ∈ entries)
    (h : check f (.factors unit entries) = true) :
    0 < entry.2 ∧ 0 < entry.1.natDegree ∧
      entry.1.leadingCoeff = 1 ∧
      (DensePoly.gcd entry.1
        (DensePoly.derivativeImpl entry.1)).natDegree = 0 := by
  have hall : entries.all (fun e =>
      0 < e.2 && 0 < e.1.natDegree &&
        decide (e.1.leadingCoeff = 1) &&
        (DensePoly.gcd e.1
          (DensePoly.derivativeImpl e.1)).natDegree == 0) = true := by
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    grind
  have he := (Array.all_eq_true_iff_forall_mem.mp hall) entry hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at he
  rcases he with ⟨⟨⟨hm, hd⟩, hlc⟩, hg⟩
  exact ⟨hm, hd, hlc, hg⟩

/-- Yun's zero result passes exact replay. -/
@[simp] theorem check_decompose_zero {K : Type u} [Lean.Grind.Field K]
    [LE K] [LT K] [Std.IsPreorder K]
    [Lean.Grind.OrderedRing K] [DecidableEq K] :
    check (0 : DensePoly K) (decompose 0) = true := by
  change check (0 : DensePoly K) (decomposeRaw 0) = true
  rw [decomposeRaw_zero]
  rfl

/-- Yun's nonzero constant result passes exact replay. -/
theorem check_decompose_constant {K : Type u} [Lean.Grind.Field K]
    [LE K] [LT K] [Std.IsPreorder K]
    [Lean.Grind.OrderedRing K] [DecidableEq K]
    (f : DensePoly K) (hzero : f ≠ 0)
    (hdegree : f.natDegree = 0) :
    check f (decompose f) = true := by
  have hsize : f.size = 1 := by
    have hs : f.size ≠ 0 := by
      intro h
      exact hzero ((DensePoly.size_eq_zero_iff f).mp h)
    have hd := hdegree
    rw [DensePoly.natDegree_eq_size_sub_one] at hd
    omega
  have hfalse : f.isZero = false :=
    (DensePoly.isZero_eq_false_iff f).2 (by omega)
  have hconstant := DensePoly.eq_C_leadingCoeff_of_size_one hsize
  have hunit : f.leadingCoeff ≠ 0 :=
    DensePoly.leadingCoeff_ne_zero_of_pos_size f (by omega)
  rw [decompose, decomposeRaw_constant f hfalse hdegree]
  have hrecon : reconstruct f.leadingCoeff #[] = f := by
    simp only [reconstruct, Array.foldl_empty]
    exact hconstant.symm
  have hsum : degreeSum (#[] : Array (DensePoly K × Nat)) = f.natDegree := by
    simp [degreeSum, hdegree]
  simp [check, hfalse, hunit, hrecon, hsum]

end Hex.RealClosure.Yun
