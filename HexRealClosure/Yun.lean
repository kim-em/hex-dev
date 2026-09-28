/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealClosure.Element
public import HexPoly.Monic
public import HexPoly.Coprime
public import HexPoly.Interpret

public section

/-!
# Yun decomposition

The executable recurrence uses the ordinary dense-polynomial operations. The
raw version supports tower coefficients whose stored equality is not value
equality. The public version requires an ordered field, hence characteristic
zero. The zero, constant and squarefree producer proofs are Mathlib-free;
the companion interprets accepted replay as mathematical factorization and
root multiplicities. The repeated-factor producer invariant remains open.
-/

namespace Hex.RealClosure.Yun

universe u v

attribute [local instance] Lean.Grind.Semiring.natCast

/-- Zero is kept separate from the scalar-times-factors result. -/
inductive Decomposition (K : Type u) [Zero K] [DecidableEq K] where
  | zero
  | factors (unit : K) (entries : Array (DensePoly K × Nat))

/-- Interpret the scalar and factors of a decomposition coefficientwise. -/
@[expose] def Decomposition.map {E : Type u} {F : Type v}
    [Zero E] [DecidableEq E] [Zero F] [DecidableEq F]
    (φ : E → F) (hz : ∀ x, φ x = 0 ↔ x = 0) :
    Decomposition E → Decomposition F
  | .zero => .zero
  | .factors unit entries =>
      .factors (φ unit) (entries.map fun entry =>
        (DensePoly.Interpret.map φ hz entry.1, entry.2))

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

/-- Yun's recurrence commutes with a zero-reflecting coefficient
interpretation. No ring laws are required of the stored coefficients. -/
theorem map_loop {E : Type u} {F : Type v}
    [Zero E] [One E] [Add E] [Sub E] [Mul E] [Div E] [Inv E]
    [NatCast E] [DecidableEq E]
    [Zero F] [One F] [Add F] [Sub F] [Mul F] [Div F] [Inv F]
    [NatCast F] [DecidableEq F]
    (φ : E → F) (hz : ∀ x, φ x = 0 ↔ x = 0)
    (hs : ∀ a b, φ (a - b) = φ a - φ b)
    (hm : ∀ a b, φ (a * b) = φ a * φ b)
    (hd : ∀ a b, φ (a / b) = φ a / φ b)
    (hi : ∀ a, φ a⁻¹ = (φ a)⁻¹)
    (hn : ∀ n : Nat, φ (n : E) = (n : F))
    (v w : DensePoly E) (i fuel : Nat)
    (out : Array (DensePoly E × Nat)) :
    (loop v w i fuel out).map (fun entry =>
      (DensePoly.Interpret.map φ hz entry.1, entry.2)) =
      loop (DensePoly.Interpret.map φ hz v)
        (DensePoly.Interpret.map φ hz w) i fuel
        (out.map fun entry =>
          (DensePoly.Interpret.map φ hz entry.1, entry.2)) := by
  induction fuel generalizing v w i out with
  | zero => rfl
  | succ fuel ih =>
      by_cases hv : v.natDegree = 0
      · simp [loop, hv, DensePoly.Interpret.map_degree]
      · have hderiv :
            DensePoly.Interpret.map φ hz (DensePoly.derivativeImpl v) =
              DensePoly.derivativeImpl (DensePoly.Interpret.map φ hz v) := by
          simpa only [← DensePoly.derivative_eq_derivativeImpl] using
            DensePoly.Interpret.map_derivative φ hz hn hm v
        have ht :
            DensePoly.Interpret.map φ hz (w - DensePoly.derivativeImpl v) =
              DensePoly.Interpret.map φ hz w -
                DensePoly.derivativeImpl (DensePoly.Interpret.map φ hz v) := by
          rw [DensePoly.Interpret.map_sub φ hz hs, hderiv]
        have hg :
            DensePoly.Interpret.map φ hz
              (DensePoly.monicize
                (DensePoly.gcd v (w - DensePoly.derivativeImpl v))) =
              DensePoly.monicize
                (DensePoly.gcd (DensePoly.Interpret.map φ hz v)
                  (DensePoly.Interpret.map φ hz w -
                    DensePoly.derivativeImpl (DensePoly.Interpret.map φ hz v))) := by
          rw [DensePoly.Interpret.map_monicize φ hz hm hi,
            DensePoly.Interpret.map_gcd φ hz hs hm hd, ht]
        simp only [loop, hv, DensePoly.Interpret.map_degree,
          ↓reduceIte]
        rw [← hg, ← ht, ← DensePoly.Interpret.map_div φ hz hs hm hd,
          ← DensePoly.Interpret.map_div φ hz hs hm hd]
        by_cases hzdeg : 0 < (DensePoly.monicize
            (DensePoly.gcd v (w - DensePoly.derivativeImpl v))).natDegree
        · simp only [DensePoly.Interpret.map_degree, hzdeg, ↓reduceIte]
          simpa only [Array.map_push] using
            ih (v / DensePoly.monicize
              (DensePoly.gcd v (w - DensePoly.derivativeImpl v)))
              ((w - DensePoly.derivativeImpl v) / DensePoly.monicize
                (DensePoly.gcd v (w - DensePoly.derivativeImpl v)))
              (i + 1)
              (out.push ((DensePoly.monicize
                (DensePoly.gcd v (w - DensePoly.derivativeImpl v))), i))
        · simp only [DensePoly.Interpret.map_degree, hzdeg, ↓reduceIte]
          exact ih _ _ _ _

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

/-- The raw Yun computation has exactly the same interpreted result as its
ordered-field counterpart whenever coefficient operations preserve values and
stored zero reflects semantic zero. -/
theorem map_decomposeRaw {E : Type u} {F : Type v}
    [Zero E] [One E] [Add E] [Sub E] [Mul E] [Div E] [Inv E]
    [NatCast E] [DecidableEq E]
    [Zero F] [One F] [Add F] [Sub F] [Mul F] [Div F] [Inv F]
    [NatCast F] [DecidableEq F]
    (φ : E → F) (hz : ∀ x, φ x = 0 ↔ x = 0)
    (hs : ∀ a b, φ (a - b) = φ a - φ b)
    (hm : ∀ a b, φ (a * b) = φ a * φ b)
    (hd : ∀ a b, φ (a / b) = φ a / φ b)
    (hi : ∀ a, φ a⁻¹ = (φ a)⁻¹)
    (hn : ∀ n : Nat, φ (n : E) = (n : F))
    (f : DensePoly E) :
    Decomposition.map φ hz (decomposeRaw f) =
      decomposeRaw (DensePoly.Interpret.map φ hz f) := by
  by_cases hf : f.isZero = true
  · simp [decomposeRaw, hf, DensePoly.Interpret.map_isZero,
      Decomposition.map]
  · have hfalse : f.isZero = false := Bool.eq_false_of_ne_true hf
    by_cases hdegree : f.natDegree = 0
    · simp [decomposeRaw, hfalse, hdegree,
        DensePoly.Interpret.map_isZero, DensePoly.Interpret.map_degree,
        DensePoly.Interpret.map_leading, Decomposition.map]
    · have hderiv :
          DensePoly.Interpret.map φ hz (DensePoly.derivativeImpl f) =
            DensePoly.derivativeImpl (DensePoly.Interpret.map φ hz f) := by
        simpa only [← DensePoly.derivative_eq_derivativeImpl] using
          DensePoly.Interpret.map_derivative φ hz hn hm f
      have ha :
          DensePoly.Interpret.map φ hz
            (DensePoly.monicize
              (DensePoly.gcd f (DensePoly.derivativeImpl f))) =
            DensePoly.monicize
              (DensePoly.gcd (DensePoly.Interpret.map φ hz f)
                (DensePoly.derivativeImpl
                  (DensePoly.Interpret.map φ hz f))) := by
        rw [DensePoly.Interpret.map_monicize φ hz hm hi,
          DensePoly.Interpret.map_gcd φ hz hs hm hd, hderiv]
      simp only [decomposeRaw, hfalse,
        DensePoly.Interpret.map_isZero,
        DensePoly.Interpret.map_degree, hdegree, ↓reduceIte,
        Decomposition.map, DensePoly.Interpret.map_leading]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [← ha, ← hderiv,
        ← DensePoly.Interpret.map_div φ hz hs hm hd,
        ← DensePoly.Interpret.map_div φ hz hs hm hd]
      have hloop := map_loop φ hz hs hm hd hi hn
          (f / DensePoly.monicize
            (DensePoly.gcd f (DensePoly.derivativeImpl f)))
          (DensePoly.derivativeImpl f / DensePoly.monicize
            (DensePoly.gcd f (DensePoly.derivativeImpl f)))
          1 (f.natDegree + 1) (#[] : Array (DensePoly E × Nat))
      simp only [Array.map_empty] at hloop
      exact congrArg
        (fun entries : Array (DensePoly F × Nat) =>
          Decomposition.factors (φ f.leadingCoeff) entries) hloop

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

private theorem divide_product {K : Type u} [Lean.Grind.Field K] [DecidableEq K]
    (f divisor quotient : DensePoly K) (hdivisor : divisor ≠ 0)
    (hproduct : quotient * divisor = f) : f / divisor = quotient := by
  rw [← hproduct]
  exact DensePoly.divMod_mul_field quotient divisor hdivisor

/-- On a squarefree input, Yun emits its monic associate once with
multiplicity one and retains its leading coefficient as the unit. -/
theorem decompose_squarefree {K : Type u} [Lean.Grind.Field K] [LE K] [LT K] [Std.IsPreorder K]
    [Lean.Grind.OrderedRing K] [DecidableEq K]
    (f : DensePoly K) (hdegree : 0 < f.natDegree)
    (hgcd : DensePoly.monicize
      (DensePoly.gcd f (DensePoly.derivativeImpl f)) = 1) :
    decompose f = .factors f.leadingCoeff #[(DensePoly.monicize f, 1)] := by
  have hf : f ≠ 0 := by
    intro h
    rw [h] at hdegree
    simp at hdegree
  have hsize : 0 < f.size := by
    apply Nat.pos_of_ne_zero
    intro h
    exact hf ((DensePoly.size_eq_zero_iff f).mp h)
  have hfalse : f.isZero = false :=
    (DensePoly.isZero_eq_false_iff f).mpr hsize
  have hlc := DensePoly.leadingCoeff_ne_zero_of_pos_size f hsize
  have hone : (1 : DensePoly K) ≠ 0 :=
    DensePoly.monic_ne_zero DensePoly.monic_one
  have hnormalized : DensePoly.monicize f ≠ 0 :=
    DensePoly.monicize_ne_zero hf
  have hproduct : DensePoly.C f.leadingCoeff * DensePoly.monicize f = f := by
    rw [← DensePoly.scale_eq_C_mul, DensePoly.monicize_eq_scale,
      DensePoly.scale_scale, Lean.Grind.Field.mul_inv_cancel hlc, DensePoly.scale_one]
  have hdivone (p : DensePoly K) : p / 1 = p :=
    divide_product p 1 p hone (DensePoly.mul_one_right_poly p)
  have hdivnormalized : f / DensePoly.monicize f = DensePoly.C f.leadingCoeff :=
    divide_product f (DensePoly.monicize f) (DensePoly.C f.leadingCoeff)
      hnormalized hproduct
  have hdivzero : (0 : DensePoly K) / DensePoly.monicize f = 0 :=
    divide_product 0 (DensePoly.monicize f) 0 hnormalized
      (DensePoly.zero_mul _)
  have hsubtract : DensePoly.derivativeImpl f - DensePoly.derivativeImpl f = 0 := by
    grind
  have hgcdzero : DensePoly.gcd f 0 = f := by
    have hz : (0 : DensePoly K).isZero = true := by rfl
    simp only [DensePoly.gcd, DensePoly.gcdAux, hz, ↓reduceDIte]
  have hnormalizedDegree : (DensePoly.monicize f).natDegree = f.natDegree := by
    rw [DensePoly.natDegree_eq_size_sub_one, DensePoly.size_monicize,
      DensePoly.natDegree_eq_size_sub_one]
  have hstop (fuel : Nat) :
      loop (DensePoly.C f.leadingCoeff) 0 2 fuel
        #[(DensePoly.monicize f, 1)] = #[(DensePoly.monicize f, 1)] := by
    cases fuel <;> simp only [loop, DensePoly.natDegree_C, ↓reduceIte]
  simp only [decompose, decomposeRaw, hfalse, Bool.false_eq_true,
    Nat.ne_of_gt hdegree, ↓reduceIte, hgcd, hdivone]
  rw [loop]
  simp only [Nat.ne_of_gt hdegree, ↓reduceIte, hsubtract, hgcdzero,
    hnormalizedDegree, hdegree, hdivnormalized, hdivzero]
  exact congrArg (Decomposition.factors f.leadingCoeff) (hstop f.natDegree)

/-- Yun's result on a squarefree input passes the exact replay checker. -/
theorem check_decompose_squarefree {K : Type u} [Lean.Grind.Field K] [LE K] [LT K] [Std.IsPreorder K]
    [Lean.Grind.OrderedRing K] [DecidableEq K]
    (f : DensePoly K) (hdegree : 0 < f.natDegree)
    (hgcd : DensePoly.monicize
      (DensePoly.gcd f (DensePoly.derivativeImpl f)) = 1) :
    check f (decompose f) = true := by
  rw [decompose_squarefree f hdegree hgcd]
  have hsize : 0 < f.size := by
    rw [DensePoly.natDegree_eq_size_sub_one] at hdegree
    omega
  have hfalse : f.isZero = false :=
    (DensePoly.isZero_eq_false_iff f).mpr hsize
  have hf : f ≠ 0 := by
    intro h
    rw [h, DensePoly.size_zero] at hsize
    omega
  have hlc := DensePoly.leadingCoeff_ne_zero_of_pos_size f hsize
  have hinv : f.leadingCoeff⁻¹ ≠ 0 := by
    intro h
    exact hlc (Lean.Grind.Field.inv_eq_zero_iff.mp h)
  have hderivative : DensePoly.derivativeImpl (DensePoly.monicize f) =
      DensePoly.scale f.leadingCoeff⁻¹ (DensePoly.derivativeImpl f) := by
    simp only [← DensePoly.derivative_eq_derivativeImpl,
      DensePoly.monicize_eq_scale]
    apply DensePoly.ext_coeff
    intro n
    simp only [DensePoly.coeff_derivative_semiring,
      DensePoly.coeff_scale_semiring]
    grind
  have hcoprime := (DensePoly.coprime_iff f (DensePoly.derivativeImpl f)).mpr hgcd
  have hscaled := ((hcoprime.scale_left hinv).symm.scale_left hinv).symm
  have hnormalizedCoprime : DensePoly.Coprime (DensePoly.monicize f)
      (DensePoly.derivativeImpl (DensePoly.monicize f)) := by
    rw [hderivative, DensePoly.monicize_eq_scale]
    exact hscaled
  have hnormalizedGcd := (DensePoly.coprime_iff (DensePoly.monicize f)
    (DensePoly.derivativeImpl (DensePoly.monicize f))).mp hnormalizedCoprime
  have hgcdDegree : (DensePoly.gcd (DensePoly.monicize f)
      (DensePoly.derivativeImpl (DensePoly.monicize f))).natDegree = 0 := by
    have h := congrArg DensePoly.natDegree hnormalizedGcd
    have honeDegree : (1 : DensePoly K).natDegree = 0 := by
      rw [DensePoly.natDegree_eq_size_sub_one,
        DensePoly.size_one (Lean.Grind.Field.zero_ne_one (α := K)).symm]
    rw [DensePoly.natDegree_eq_size_sub_one, DensePoly.size_monicize,
      ← DensePoly.natDegree_eq_size_sub_one, honeDegree] at h
    exact h
  have hnormalizedDegree : (DensePoly.monicize f).natDegree = f.natDegree := by
    rw [DensePoly.natDegree_eq_size_sub_one, DensePoly.size_monicize,
      DensePoly.natDegree_eq_size_sub_one]
  have hmonic : (DensePoly.monicize f).leadingCoeff = 1 :=
    DensePoly.monicize_monic hf
  have hrecon : reconstruct f.leadingCoeff #[(DensePoly.monicize f, 1)] = f := by
    simp only [reconstruct, ← Array.foldl_toList]
    change DensePoly.C f.leadingCoeff * (DensePoly.monicize f) ^ 1 = f
    rw [Lean.Grind.Semiring.pow_one, ← DensePoly.scale_eq_C_mul,
      DensePoly.monicize_eq_scale, DensePoly.scale_scale,
      Lean.Grind.Field.mul_inv_cancel hlc, DensePoly.scale_one]
  simp [check, hfalse, hnormalizedDegree, hdegree, hmonic,
    hgcdDegree, hrecon, degreeSum]
  exact hlc

end Hex.RealClosure.Yun

/-- info: 'Hex.RealClosure.Yun.check_decompose_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.check_decompose_zero
/-- info: 'Hex.RealClosure.Yun.check_decompose_constant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.check_decompose_constant

/-- info: 'Hex.RealClosure.Yun.map_decomposeRaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.map_decomposeRaw

/-- info: 'Hex.RealClosure.Yun.decompose_squarefree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.decompose_squarefree
/-- info: 'Hex.RealClosure.Yun.check_decompose_squarefree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.check_decompose_squarefree
