/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvGcd.Gcd

@[expose] public section
set_option backward.proofsInPublic true

/-!
Squarefree decision and characteristic-zero decomposition.

The exact Boolean decision works over perfect coefficient fraction fields,
including bounded prime fields.  The executable decomposition remains
characteristic-zero: it follows the named-variable recursive form of Yun's
algorithm.  Coefficient content is decomposed one arity down; the primitive
part is split into its multiplicity layers using one selected main variable,
and equal-multiplicity factors are merged.  Scalar content is kept separately,
matching the computer-algebra convention over `Int`.
-/

namespace Hex.MvPoly

universe u

/-- Mathlib-free characteristic zero. -/
class NatNoZero (R : Type u) [Zero R] [NatCast R] : Prop where
  natCast_ne_zero : ∀ m : Nat, 0 < m → (m : R) ≠ 0

instance instNatNoZeroInt : NatNoZero Int := by
  constructor
  intro m hm
  omega

instance instNatNoZeroRat : NatNoZero Rat := by
  constructor
  intro m hm
  sorry

instance instFractionNonzeroOneInt : Hex.Fraction.NonzeroOne Int :=
  ⟨by decide⟩

instance instFractionNonzeroOneRat : Hex.Fraction.NonzeroOne Rat :=
  ⟨by decide⟩

/-- Bounded prime residues are nontrivial.  The lower priority retains a
coherent instance for the carrier's direct ring operations while allowing the
generic field bridge below to serve inherited field-operation diamonds. -/
instance (priority := 50) instFractionNonzeroOneZMod64 {p : Nat}
    [hp : ZMod64.Bounds p] [ZMod64.PrimeModulus p] :
    Hex.Fraction.NonzeroOne (@ZMod64 p hp) :=
  ⟨ZMod64.one_ne_zero_of_prime (ZMod64.PrimeModulus.prime (p := p))⟩

/-- Every lightweight field supplies the nontriviality needed by the fraction
construction.  Keeping this bridge generic also makes the inherited field
operations coherent when a carrier has a separately declared ring instance. -/
instance instFractionNonzeroOneField {K : Type u} [Lean.Grind.Field K] :
    Hex.Fraction.NonzeroOne K :=
  ⟨fun h => Lean.Grind.Field.zero_ne_one h.symm⟩

/-- The coefficient fraction field is perfect.  This is used only by the
semantic decision theorem; the Boolean checker itself uses gcd replay. -/
class PerfectFrac (R : Type u) [Lean.Grind.CommRing R] [Div R]
    [ExactDivLaws R] [Hex.Fraction.NonzeroOne R] : Prop where
  charZeroOrPerfect :
    (∀ m : Nat, 0 < m → (m : Hex.Fraction R) ≠ 0) ∨
    ∃ p : Nat, Hex.Nat.Prime p ∧ (p : Hex.Fraction R) = 0 ∧
      ∀ a : Hex.Fraction R, ∃ b : Hex.Fraction R, b ^ p = a

instance instPerfectFracInt : PerfectFrac Int := by
  constructor
  left
  intro m hm
  sorry

instance instPerfectFracRat : PerfectFrac Rat := by
  constructor
  left
  intro m hm
  sorry

/-- The fraction field of a bounded prime field is perfect.  Every fraction is
represented by a coefficient because its denominator is invertible, and
Fermat's theorem makes the `p`th-power map the identity on those coefficients.
-/
instance instPerfectFracZMod64 {p : Nat} [hp : ZMod64.Bounds p]
    [ZMod64.PrimeModulus p] :
    PerfectFrac (@ZMod64 p hp) := by
  constructor
  right
  refine ⟨p, ZMod64.PrimeModulus.prime (p := p), ?_, ?_⟩
  · change Hex.Fraction.ofCoeff (p : ZMod64 p) = 0
    rw [ZMod64.natCast_self]
    exact Hex.Fraction.ofCoeff_zero
  · intro a
    induction a using Quotient.inductionOn with
    | _ a =>
        let q := a.num / a.den
        refine ⟨Hex.Fraction.ofCoeff q, ?_⟩
        rw [← Hex.Fraction.ofCoeff_pow, ZMod64.pow_prime_of_prime_modulus]
        apply Quotient.sound
        change (a.num / a.den) * a.den = a.num * 1
        rw [Lean.Grind.Field.div_eq_mul_inv, Lean.Grind.Semiring.mul_assoc,
          Lean.Grind.Field.inv_mul_cancel a.den_ne,
          Lean.Grind.Semiring.mul_one]

/-- A polynomial has no variable in its support. -/
def IsConst {n : Nat} {R : Type u} [Zero R]
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (p : MvPoly n R cmp) : Prop :=
  p.vars = []

/-- Relative squarefreeness: repeated divisors must be constant. -/
def Squarefree {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R]
    (p : MvPoly n R cmp) : Prop :=
  p ≠ 0 ∧ ∀ d, d * d ∣ p → IsConst d

structure SqfFactor (n : Nat) (R : Type u) [Zero R]
    (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] where
  factor : MvPoly n R cmp
  multiplicity : Nat

structure SqfDecomp (n : Nat) (R : Type u) [Zero R]
    (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] where
  content : R
  factors : List (SqfFactor n R cmp)

variable {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
  [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
  [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
  [GcdProducer R]

/-- All partial derivatives, in variable-index order. -/
def derivatives [NatCast R] (p : MvPoly n R cmp) : List (MvPoly n R cmp) :=
  (List.finRange n).map fun i => derivative i p

/-- Merge one factor into the multiplicity-sorted accumulator, multiplying
factors when the recursive content decomposition and the main-variable Yun
decomposition contribute at the same multiplicity. -/
def mergeSqfFactor (entry : SqfFactor n R cmp) :
    List (SqfFactor n R cmp) → List (SqfFactor n R cmp)
  | [] => [entry]
  | head :: tail =>
      if entry.multiplicity < head.multiplicity then entry :: head :: tail
      else if entry.multiplicity = head.multiplicity then
        { factor := entry.factor * head.factor
          multiplicity := entry.multiplicity } :: tail
      else head :: mergeSqfFactor entry tail

/-- One decreasing Yun layer in the selected main variable.  The fuel is the
total degree of the primitive input plus one; in characteristic zero every
nonterminal layer removes at least one degree from `b`. -/
def yunLoop [NatCast R] [IsMonomialOrder cmp] (i : Fin n) (fuel k : Nat)
    (b d : MvPoly n R cmp) (acc : List (SqfFactor n R cmp)) :
    List (SqfFactor n R cmp) :=
  match fuel with
  | 0 => acc.reverse
  | fuel + 1 =>
      if polyIsUnit b then acc.reverse
      else
        let factor := gcd b d
        let nextB := quotient b factor
        let nextC := quotient d factor
        let nextD := nextC - derivative i nextB
        let acc := if polyIsUnit factor then acc else ⟨factor, k⟩ :: acc
        yunLoop i fuel (k + 1) nextB nextD acc

/-- Move the normalization unit of the primitive part into the scalar output,
so the polynomial sent to recursive decomposition is canonically normalized
without losing the sign (or general coefficient-ring unit) in the product. -/
def sqfPrimitiveSplit [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) : R × MvPoly n R cmp :=
  let scalar := content p
  let primitive := primPart p
  let unitInv := GcdOps.exactDiv 1 (GcdOps.normUnit primitive.leadingCoeff)
  (scalar * unitInv, polyNormalize primitive)

/-- Arity-indexed decomposition operation.  Packaging the recursive call
makes the coefficient-content descent structurally decreasing in the arity. -/
structure SqfOpsAt (R : Type u) [Zero R] (n : Nat) : Type (u + 1) where
  decomp : (cmp : Mono n → Mono n → Ordering) →
    [IsMonomialOrder cmp] → MvPoly n R cmp → SqfDecomp n R cmp

/-- The arity-zero polynomial is a scalar, including its normalization unit. -/
def sqfBase : SqfOpsAt R 0 where
  decomp := fun _ _ p =>
    let split := sqfPrimitiveSplit p
    ⟨split.1, []⟩

/-- One recursive content split followed by Yun in a variable which occurs in
the normalized primitive part. -/
def sqfStep [NatCast R] {m : Nat} (lower : SqfOpsAt R m) :
    SqfOpsAt R (m + 1) where
  decomp := fun cmp _ p =>
    let split := sqfPrimitiveSplit p
    let scalar := split.1
    let q := split.2
    if q == 0 || polyIsUnit q then
      ⟨scalar, []⟩
    else
      match q.vars with
      | [] => ⟨scalar, []⟩
      | i :: _ =>
          let coefficientPart := contentIn i Mono.lex q
          let coefficientDecomp := lower.decomp Mono.lex coefficientPart
          let mainPart := primPartIn i Mono.lex q
          let deriv := derivative i mainPart
          let repeated := gcd mainPart deriv
          let b := quotient mainPart repeated
          let c := quotient deriv repeated
          let d := c - derivative i b
          let mainFactors :=
            yunLoop i (mainPart.totalDegree + 1) 1 b d []
          let liftedFactors := coefficientDecomp.factors.map fun factor =>
            { factor := constIn (cmp := cmp) i Mono.lex factor.factor
              multiplicity := factor.multiplicity }
          let factors := liftedFactors.foldl
            (fun acc factor => mergeSqfFactor factor acc) mainFactors
          ⟨scalar * coefficientDecomp.content, factors⟩

/-- Construct squarefree decomposition recursively in the arity. -/
def sqfOps [NatCast R] : (m : Nat) → SqfOpsAt R m
  | 0 => sqfBase
  | m + 1 => sqfStep (sqfOps m)

/-- Characteristic-zero squarefree decomposition with recursive content and
scalar content split off. -/
def sqfDecomp [IsMonomialOrder cmp] [NatCast R] [NatNoZero R]
    (p : MvPoly n R cmp) : SqfDecomp n R cmp :=
  (sqfOps (R := R) n).decomp cmp p

/-- Product of the distinct polynomial factors; scalar content is omitted. -/
def radical [IsMonomialOrder cmp] [NatCast R] [NatNoZero R]
    (p : MvPoly n R cmp) : MvPoly n R cmp :=
  let q := polyNormalize (primPart p)
  if q == 0 then 0
  else quotient q (gcdList (q :: derivatives q))

/-- Exact Boolean squarefree decision under the relative CAS convention. -/
def isSquarefree [IsMonomialOrder cmp] [NatCast R]
    (p : MvPoly n R cmp) : Bool :=
  let q := primPart p
  polyIsUnit (gcdList (q :: derivatives q))

theorem isSquarefree_iff [IsMonomialOrder cmp] [NatCast R]
    [Div R] [ExactDivLaws R] [Hex.Fraction.NonzeroOne R] [PerfectFrac R]
    (p : MvPoly n R cmp) :
    isSquarefree p = true ↔ Squarefree p := by
  sorry

theorem radical_squarefree [IsMonomialOrder cmp] [NatCast R] [NatNoZero R]
    (p : MvPoly n R cmp) (hp : p ≠ 0) : Squarefree (radical p) := by
  sorry

theorem radical_dvd [IsMonomialOrder cmp] [NatCast R] [NatNoZero R]
    (p : MvPoly n R cmp) : radical p ∣ p := by
  sorry

@[simp] theorem radical_zero [IsMonomialOrder cmp] [NatCast R] [NatNoZero R] :
    radical (0 : MvPoly n R cmp) = 0 := by
  sorry

theorem sqfDecomp_prod [IsMonomialOrder cmp] [NatCast R] [NatNoZero R]
    (p : MvPoly n R cmp) :
    (sqfDecomp p).factors.foldl
      (fun acc f => acc * f.factor ^ f.multiplicity)
      (C (sqfDecomp p).content) = p := by
  sorry

theorem sqfDecomp_squarefree [IsMonomialOrder cmp] [NatCast R] [NatNoZero R]
    (p : MvPoly n R cmp) :
    ∀ f ∈ (sqfDecomp p).factors, Squarefree f.factor := by
  sorry

theorem sqfDecomp_primitive [IsMonomialOrder cmp] [NatCast R] [NatNoZero R]
    (p : MvPoly n R cmp) :
    ∀ f ∈ (sqfDecomp p).factors, content f.factor = 1 := by
  sorry

theorem sqfDecomp_coprime [IsMonomialOrder cmp] [NatCast R] [NatNoZero R]
    (p : MvPoly n R cmp) :
    ∀ f ∈ (sqfDecomp p).factors, ∀ g ∈ (sqfDecomp p).factors,
      f.multiplicity ≠ g.multiplicity →
        ∀ d, d ∣ f.factor → d ∣ g.factor → GcdOps.isUnit d = true := by
  sorry

theorem sqfDecomp_multiplicity_pos [IsMonomialOrder cmp]
    [NatCast R] [NatNoZero R] (p : MvPoly n R cmp) :
    ∀ f ∈ (sqfDecomp p).factors, 0 < f.multiplicity := by
  sorry

theorem sqfDecomp_multiplicity_sorted [IsMonomialOrder cmp]
    [NatCast R] [NatNoZero R] (p : MvPoly n R cmp) :
    List.Pairwise (fun f g => f.multiplicity < g.multiplicity)
      (sqfDecomp p).factors := by
  sorry

theorem sqfDecomp_nonconstant [IsMonomialOrder cmp]
    [NatCast R] [NatNoZero R] (p : MvPoly n R cmp) :
    ∀ f ∈ (sqfDecomp p).factors, ¬ IsConst f.factor := by
  sorry

end Hex.MvPoly
