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
  change ((m : Int) : Rat) ≠ 0
  intro h
  have : (m : Int) = 0 := Rat.intCast_eq_zero_iff.mp h
  omega

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
  change Hex.Fraction.ofCoeff (m : Int) ≠ 0
  intro h
  have : (m : Int) = 0 := (Hex.Fraction.ofCoeff_eq_zero_iff _).mp h
  omega

instance instPerfectFracRat : PerfectFrac Rat := by
  constructor
  left
  intro m hm
  change Hex.Fraction.ofCoeff (m : Rat) ≠ 0
  intro h
  have hrat : (m : Rat) = 0 := (Hex.Fraction.ofCoeff_eq_zero_iff _).mp h
  exact NatNoZero.natCast_ne_zero m hm hrat

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

/-- Scalar content and the multiplicity-tagged square-free polynomial factors. -/
structure SqfDecomp (n : Nat) (R : Type u) [Zero R]
    (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] where
  /-- Scalar content separated from the polynomial factors. -/
  content : R
  /-- Distinct square-free factors paired with their multiplicities. -/
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

private def PositiveMultiplicities (factors : List (SqfFactor n R cmp)) : Prop :=
  ∀ factor ∈ factors, 0 < factor.multiplicity

omit [DecidableEq R] [Dvd R] [BezoutOps R] [LawfulGcdOps R]
    [LawfulBezoutOps R] [GcdProducer R] in
private theorem positive_merge (entry : SqfFactor n R cmp)
    (hentry : 0 < entry.multiplicity) {factors : List (SqfFactor n R cmp)}
    (hfactors : PositiveMultiplicities factors) :
    PositiveMultiplicities (mergeSqfFactor entry factors) := by
  induction factors with
  | nil => simpa [PositiveMultiplicities, mergeSqfFactor]
  | cons head tail ih =>
      simp only [mergeSqfFactor]
      split
      · simp_all [PositiveMultiplicities]
      · split
        · simp_all [PositiveMultiplicities]
        · simp_all [PositiveMultiplicities]

omit [DecidableEq R] [Dvd R] [BezoutOps R] [LawfulGcdOps R]
    [LawfulBezoutOps R] [GcdProducer R] in
private theorem positive_merge_fold (entries acc : List (SqfFactor n R cmp))
    (hentries : PositiveMultiplicities entries)
    (hacc : PositiveMultiplicities acc) :
    PositiveMultiplicities (entries.foldl
      (fun acc entry => mergeSqfFactor entry acc) acc) := by
  induction entries generalizing acc with
  | nil => simpa
  | cons entry entries ih =>
      simp only [List.foldl_cons]
      have hentries' : 0 < entry.multiplicity ∧
          PositiveMultiplicities entries := by
        simpa [PositiveMultiplicities] using hentries
      apply ih
      · exact hentries'.2
      · apply positive_merge entry
        · exact hentries'.1
        · exact hacc

private def MultiplicitiesAbove (bound : Nat)
    (factors : List (SqfFactor n R cmp)) : Prop :=
  ∀ factor ∈ factors, bound < factor.multiplicity

private def SortedMultiplicities (factors : List (SqfFactor n R cmp)) : Prop :=
  factors.Pairwise fun left right => left.multiplicity < right.multiplicity

omit [DecidableEq R] [Dvd R] [BezoutOps R] [LawfulGcdOps R]
    [LawfulBezoutOps R] [GcdProducer R] in
private theorem above_merge (bound : Nat) (entry : SqfFactor n R cmp)
    (hentry : bound < entry.multiplicity) {factors : List (SqfFactor n R cmp)}
    (hfactors : MultiplicitiesAbove bound factors) :
    MultiplicitiesAbove bound (mergeSqfFactor entry factors) := by
  induction factors with
  | nil => simpa [MultiplicitiesAbove, mergeSqfFactor]
  | cons head tail ih =>
      simp only [mergeSqfFactor]
      split
      · simp_all [MultiplicitiesAbove]
      · split
        · simp_all [MultiplicitiesAbove]
        · simp_all [MultiplicitiesAbove]

omit [DecidableEq R] [Dvd R] [BezoutOps R] [LawfulGcdOps R]
    [LawfulBezoutOps R] [GcdProducer R] in
private theorem sorted_merge (entry : SqfFactor n R cmp)
    {factors : List (SqfFactor n R cmp)}
    (hfactors : SortedMultiplicities factors) :
    SortedMultiplicities (mergeSqfFactor entry factors) := by
  induction factors with
  | nil => simp [SortedMultiplicities, mergeSqfFactor]
  | cons head tail ih =>
      have hsorted : MultiplicitiesAbove head.multiplicity tail ∧
          SortedMultiplicities tail := by
        simpa [MultiplicitiesAbove, SortedMultiplicities] using hfactors
      simp only [mergeSqfFactor]
      split <;> rename_i hlt
      · apply List.Pairwise.cons
        · intro factor hfactor
          simp only [List.mem_cons] at hfactor
          rcases hfactor with rfl | hfactor
          · exact hlt
          · exact Nat.lt_trans hlt (hsorted.1 factor hfactor)
        · exact hfactors
      · split <;> rename_i heq
        · apply List.Pairwise.cons
          · intro factor hfactor
            simpa [heq] using hsorted.1 factor hfactor
          · exact hsorted.2
        · apply List.Pairwise.cons
          · apply above_merge
            · omega
            · exact hsorted.1
          · exact ih hsorted.2

omit [DecidableEq R] [Dvd R] [BezoutOps R] [LawfulGcdOps R]
    [LawfulBezoutOps R] [GcdProducer R] in
private theorem sorted_merge_fold (entries acc : List (SqfFactor n R cmp))
    (hacc : SortedMultiplicities acc) :
    SortedMultiplicities (entries.foldl
      (fun acc entry => mergeSqfFactor entry acc) acc) := by
  induction entries generalizing acc with
  | nil => simpa
  | cons entry entries ih =>
      simp only [List.foldl_cons]
      exact ih _ (sorted_merge entry hacc)

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

omit [LawfulGcdOps R] [LawfulBezoutOps R] in
private theorem positive_yunLoop [NatCast R] [IsMonomialOrder cmp]
    (i : Fin n) (fuel k : Nat) (b d : MvPoly n R cmp)
    (acc : List (SqfFactor n R cmp)) (hk : 0 < k)
    (hacc : PositiveMultiplicities acc) :
    PositiveMultiplicities (yunLoop i fuel k b d acc) := by
  induction fuel generalizing k b d acc with
  | zero => simpa [yunLoop, PositiveMultiplicities] using hacc
  | succ fuel ih =>
      simp only [yunLoop]
      split
      · simpa [PositiveMultiplicities] using hacc
      · apply ih
        · omega
        · split
          · exact hacc
          · simpa [PositiveMultiplicities] using And.intro hk hacc

private def MultiplicitiesBelow (bound : Nat)
    (factors : List (SqfFactor n R cmp)) : Prop :=
  ∀ factor ∈ factors, factor.multiplicity < bound

private def ReverseSortedMultiplicities
    (factors : List (SqfFactor n R cmp)) : Prop :=
  factors.Pairwise fun left right => right.multiplicity < left.multiplicity

omit [LawfulGcdOps R] [LawfulBezoutOps R] in
private theorem sorted_yunLoop [NatCast R] [IsMonomialOrder cmp]
    (i : Fin n) (fuel k : Nat) (b d : MvPoly n R cmp)
    (acc : List (SqfFactor n R cmp))
    (hbelow : MultiplicitiesBelow k acc)
    (hsorted : ReverseSortedMultiplicities acc) :
    SortedMultiplicities (yunLoop i fuel k b d acc) := by
  induction fuel generalizing k b d acc with
  | zero =>
      unfold SortedMultiplicities
      rw [yunLoop, List.pairwise_reverse]
      exact hsorted
  | succ fuel ih =>
      simp only [yunLoop]
      split
      · unfold SortedMultiplicities
        rw [List.pairwise_reverse]
        exact hsorted
      · split
        · apply ih
          · intro factor hfactor
            exact Nat.lt_trans (hbelow factor hfactor) (Nat.lt_succ_self k)
          · exact hsorted
        · apply ih
          · intro factor hfactor
            simp only [List.mem_cons] at hfactor
            rcases hfactor with rfl | hfactor
            · change k < k + 1
              omega
            · exact Nat.lt_trans (hbelow factor hfactor) (Nat.lt_succ_self k)
          · apply List.Pairwise.cons
            · exact hbelow
            · exact hsorted

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

omit [LawfulGcdOps R] [LawfulBezoutOps R] in
private theorem positive_sqfOps [NatCast R] (m : Nat)
    (order : Mono m → Mono m → Ordering) [IsMonomialOrder order]
    (p : MvPoly m R order) :
    PositiveMultiplicities ((sqfOps (R := R) m).decomp order p).factors := by
  induction m with
  | zero => simp [sqfOps, sqfBase, sqfPrimitiveSplit, PositiveMultiplicities]
  | succ m ih =>
      simp only [sqfOps, sqfStep]
      split
      · simp [PositiveMultiplicities]
      · cases hvars : p.sqfPrimitiveSplit.2.vars with
        | nil => simp [PositiveMultiplicities]
        | cons i tail =>
            apply positive_merge_fold
            · have hlower := ih Mono.lex
                (contentIn i Mono.lex p.sqfPrimitiveSplit.2)
              simpa [PositiveMultiplicities] using hlower
            · apply positive_yunLoop
              · omega
              · simp [PositiveMultiplicities]

omit [LawfulGcdOps R] [LawfulBezoutOps R] in
private theorem sorted_sqfOps [NatCast R] (m : Nat)
    (order : Mono m → Mono m → Ordering) [IsMonomialOrder order]
    (p : MvPoly m R order) :
    SortedMultiplicities ((sqfOps (R := R) m).decomp order p).factors := by
  cases m with
  | zero => simp [sqfOps, sqfBase, sqfPrimitiveSplit, SortedMultiplicities]
  | succ m =>
      simp only [sqfOps, sqfStep]
      split
      · simp [SortedMultiplicities]
      · cases hvars : p.sqfPrimitiveSplit.2.vars with
        | nil => simp [SortedMultiplicities]
        | cons i tail =>
            apply sorted_merge_fold
            apply sorted_yunLoop
            · simp [MultiplicitiesBelow]
            · simp [ReverseSortedMultiplicities]

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

omit [LawfulGcdOps R] [LawfulBezoutOps R] in
@[simp] theorem radical_zero [IsMonomialOrder cmp] [NatCast R] [NatNoZero R] :
    radical (0 : MvPoly n R cmp) = 0 := by
  simp [radical]

/-- Multiplying the scalar and factor powers reconstructs the input. -/
theorem sqfDecomp_prod [IsMonomialOrder cmp] [NatCast R] [NatNoZero R]
    (p : MvPoly n R cmp) :
    (sqfDecomp p).factors.foldl
      (fun acc f => acc * f.factor ^ f.multiplicity)
      (C (sqfDecomp p).content) = p := by
  sorry

/-- Every polynomial returned by square-free decomposition is square-free. -/
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

omit [LawfulGcdOps R] [LawfulBezoutOps R] in
theorem sqfDecomp_multiplicity_pos [IsMonomialOrder cmp]
    [NatCast R] [NatNoZero R] (p : MvPoly n R cmp) :
    ∀ f ∈ (sqfDecomp p).factors, 0 < f.multiplicity := by
  simpa [sqfDecomp, PositiveMultiplicities] using
    positive_sqfOps (R := R) n cmp p

omit [LawfulGcdOps R] [LawfulBezoutOps R] in
theorem sqfDecomp_multiplicity_sorted [IsMonomialOrder cmp]
    [NatCast R] [NatNoZero R] (p : MvPoly n R cmp) :
    List.Pairwise (fun f g => f.multiplicity < g.multiplicity)
      (sqfDecomp p).factors := by
  simpa [sqfDecomp, SortedMultiplicities] using
    sorted_sqfOps (R := R) n cmp p

theorem sqfDecomp_nonconstant [IsMonomialOrder cmp]
    [NatCast R] [NatNoZero R] (p : MvPoly n R cmp) :
    ∀ f ∈ (sqfDecomp p).factors, ¬ IsConst f.factor := by
  sorry

end Hex.MvPoly
