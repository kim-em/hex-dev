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

attribute [local instance] Lean.Grind.Semiring.natCast
attribute [local instance] Lean.Grind.Ring.intCast

/-- Mathlib-free characteristic zero for the coefficient ring's own natural cast. -/
class NatNoZero (R : Type u) [Lean.Grind.CommRing R] : Prop where
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
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
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

/-- All partial derivatives, in variable-index order, using the coefficient
ring's natural cast. -/
def derivatives (p : MvPoly n R cmp) : List (MvPoly n R cmp) :=
  (List.finRange n).map fun i => derivative i p

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
/-- Differentiation commutes with the recursive univariate view in the
selected variable. -/
theorem toUnivariate_derivative {m : Nat}
    {cmp0 : Mono (m + 1) → Mono (m + 1) → Ordering}
    {cmp' : Mono m → Mono m → Ordering}
    [Std.TransCmp cmp0] [Std.LawfulEqCmp cmp0]
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    (i : Fin (m + 1)) (p : MvPoly (m + 1) R cmp0) :
    toUnivariate i cmp' (derivative i p) =
      DensePoly.derivative (toUnivariate i cmp' p) := by
  apply DensePoly.ext_coeff
  intro e
  apply MvPoly.ext
  intro a
  have hsucc : Mono.succAt i (insertVar i e a) =
      insertVar i (e + 1) a := by
    apply Vector.ext
    intro j hj
    by_cases hjval : j = i.val
    · simp [Mono.succAt, Mono.mul, Mono.unit, insertVar, hjval]
    · have hfin : (⟨j, hj⟩ : Fin (m + 1)) ≠ i := by
        intro h
        exact hjval (congrArg Fin.val h)
      simp [Mono.succAt, Mono.mul, Mono.unit, insertVar, hjval, hfin]
  have hcast : ((e + 1 : Nat) : MvPoly m R cmp') =
      C ((e + 1 : Nat) : R) := by
    apply MvPoly.ext
    intro b
    simp only [coeff_natCast, coeff_C]
  rw [toUnivariate_coeff, coeff_derivative,
    DensePoly.coeff_derivative_semiring, degreeOf_insertVar, hsucc,
    hcast, coeff_C_mul, toUnivariate_coeff]

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
/-- Formal partial differentiation satisfies the product rule. -/
theorem derivative_mul (i : Fin n) (p q : MvPoly n R cmp) :
    derivative i (p * q) =
      derivative i p * q + p * derivative i q := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ m =>
      have hview :
          toUnivariate i Mono.lex (derivative i (p * q)) =
            toUnivariate i Mono.lex
              (derivative i p * q + p * derivative i q) := by
        rw [toUnivariate_derivative, toUnivariate_mul,
          DensePoly.derivative_mul, toUnivariate_add,
          toUnivariate_mul, toUnivariate_mul,
          toUnivariate_derivative, toUnivariate_derivative]
      calc
        derivative i (p * q) =
            ofUnivariate i Mono.lex
              (toUnivariate i Mono.lex (derivative i (p * q))) :=
          (ofUnivariate_toUnivariate i _).symm
        _ = ofUnivariate i Mono.lex
              (toUnivariate i Mono.lex
                (derivative i p * q + p * derivative i q)) := by rw [hview]
        _ = derivative i p * q + p * derivative i q :=
          ofUnivariate_toUnivariate i _

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
@[simp] private theorem mvDerivative_zero (i : Fin n) :
    derivative i (0 : MvPoly n R cmp) = 0 := by
  apply MvPoly.ext
  intro m
  rw [coeff_derivative, coeff_zero, Lean.Grind.Semiring.mul_zero, coeff_zero]

omit [LawfulBezoutOps R] [GcdProducer R] in
/-- A nonzero polynomial cannot divide a nonzero partial derivative of
itself: the selected-variable degree drops strictly. -/
theorem derivative_eq_zero_of_dvd (i : Fin n)
    (p : MvPoly n R cmp) (hp : p ≠ 0) (hdiv : p ∣ derivative i p) :
    derivative i p = 0 := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ m =>
      by_cases hderiv : derivative i p = 0
      · exact hderiv
      exfalso
      rcases hdiv with ⟨q, hq⟩
      have hq0 : q ≠ 0 := by
        intro hzero
        apply hderiv
        rw [hq, hzero, MvPoly.zero_mul]
      let pv := toUnivariate i Mono.lex p
      let qv := toUnivariate i Mono.lex q
      have hpv0 : pv ≠ 0 := by
        intro hzero
        apply hp
        calc
          p = ofUnivariate i Mono.lex pv :=
            (ofUnivariate_toUnivariate i p).symm
          _ = 0 := by rw [hzero]; rfl
      have hqv0 : qv ≠ 0 := by
        intro hzero
        apply hq0
        calc
          q = ofUnivariate i Mono.lex qv :=
            (ofUnivariate_toUnivariate i q).symm
          _ = 0 := by rw [hzero]; rfl
      have hpvPos : 0 < pv.size := by
        exact Nat.pos_of_ne_zero (fun h => hpv0 ((DensePoly.size_eq_zero_iff pv).mp h))
      have hqvPos : 0 < qv.size := by
        exact Nat.pos_of_ne_zero (fun h => hqv0 ((DensePoly.size_eq_zero_iff qv).mp h))
      have htop : qv.leadingCoeff * pv.leadingCoeff ≠
          (0 : MvPoly m R Mono.lex) := by
        intro hzero
        rcases MvPoly.zero_product GcdDomainLaws.no_zero_div hzero with
          hqlead | hplead
        · exact (DensePoly.leadingCoeff_ne_zero_of_pos_size qv hqvPos) hqlead
        · exact (DensePoly.leadingCoeff_ne_zero_of_pos_size pv hpvPos) hplead
      have hproduct :
          (toUnivariate i Mono.lex (derivative i p)).size =
            qv.size + pv.size - 1 := by
        rw [hq, toUnivariate_mul]
        exact DensePoly.size_mul_of_top_ne qv pv hqvPos hpvPos htop
      have hdrop :
          (toUnivariate i Mono.lex (derivative i p)).size ≤ pv.size - 1 := by
        rw [toUnivariate_derivative]
        exact DensePoly.size_derivative_le pv
      omega

omit [LawfulBezoutOps R] [GcdProducer R] in
/-- In characteristic zero, vanishing of every partial derivative forces a
polynomial to be constant. -/
private theorem isConst_of_derivatives_zero [NatNoZero R]
    (p : MvPoly n R cmp) (hderiv : ∀ i, derivative i p = 0) :
    IsConst p := by
  have hmono : ∀ m ∈ p.monomials, m = Mono.zero := by
    intro m hm
    apply Vector.ext
    intro j hj
    let i : Fin n := ⟨j, hj⟩
    change m[i] = (Mono.zero : Mono n)[i]
    rw [Mono.getElem_zero]
    change Mono.degreeOf i m = 0
    by_cases he : Mono.degreeOf i m = 0
    · exact he
    exfalso
    have hsucc : Mono.succAt i (predAt i m) = m := by
      exact ((predAt_eq_iff i (predAt i m) m he).mp rfl).symm
    have hdegree := congrArg (Mono.degreeOf i) hsucc
    rw [degreeOf_succAt] at hdegree
    have hcoeff := congrArg (coeff (predAt i m)) (hderiv i)
    rw [coeff_derivative, coeff_zero, hsucc] at hcoeff
    have hcast : ((Mono.degreeOf i (predAt i m) + 1 : Nat) : R) ≠ 0 :=
      NatNoZero.natCast_ne_zero _ (by omega)
    have hmcoeff : coeff m p ≠ 0 := (mem_monomials_iff m p).mp hm
    rcases LawfulGcdOps.no_zero_div
        (((Mono.degreeOf i (predAt i m) + 1 : Nat) : R))
        (coeff m p) hcoeff with hzero | hzero
    · exact hcast hzero
    · exact hmcoeff hzero
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro i hi
  have hdegree : degreeOf i p = 0 := by
    rw [degreeOf_eq]
    unfold foldTerms
    rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
    have hterm : ∀ term ∈ p.termsList, Mono.degreeOf i term.1 = 0 := by
      intro term ht
      have hm : term.1 ∈ p.monomials := by
        exact List.mem_map.mpr ⟨term, ht, rfl⟩
      rw [hmono term.1 hm]
      exact Mono.getElem_zero i
    have fold_zero : ∀ (terms : List (Mono n × R)),
        (∀ term ∈ terms, Mono.degreeOf i term.1 = 0) →
          terms.foldl (fun d term => max d (Mono.degreeOf i term.1)) 0 = 0 := by
      intro terms hall
      induction terms with
      | nil => rfl
      | cons head tail ih =>
          rw [List.foldl_cons, hall head (by simp), Nat.max_zero]
          apply ih
          intro term ht
          exact hall term (by simp [ht])
    exact fold_zero p.termsList hterm
  exact ((mem_vars_iff i p).mp hi) hdegree

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
private theorem isConst_C (c : R) : IsConst (C c : MvPoly n R cmp) := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro i hi
  have hne := (mem_vars_iff i (C c : MvPoly n R cmp)).mp hi
  apply hne
  change degreeOf i (monomial Mono.zero c : MvPoly n R cmp) = 0
  rw [degreeOf_monomial]
  split
  · rfl
  · exact Mono.getElem_zero i

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
theorem C_mul_C (a b : R) :
    (C a : MvPoly n R cmp) * C b = C (a * b) := by
  apply MvPoly.ext
  intro m
  rw [coeff_C_mul, coeff_C, coeff_C]
  by_cases hm : m = Mono.zero
  · simp [hm]
  · rw [ite_eq_right hm, ite_eq_right hm,
      Lean.Grind.Semiring.mul_zero]

omit [LawfulBezoutOps R] [GcdProducer R] in
/-- Removing scalar content preserves the relative squarefree predicate. -/
theorem squarefree_primPart (p : MvPoly n R cmp) :
    Squarefree (primPart p) ↔ Squarefree p := by
  constructor
  · intro hq
    refine ⟨?_, ?_⟩
    · intro hp0
      subst p
      exact hq.1 primPart_zero
    · intro d hd
      rcases hd with ⟨a, ha⟩
      have hparts := congrArg primPart ha
      rw [primPart_mul a (d * d), primPart_mul d d] at hparts
      have hsquare : primPart d * primPart d ∣ primPart p :=
        ⟨primPart a, hparts⟩
      have hconst := hq.2 (primPart d) hsquare
      have hdrec := content_mul_primPart d
      have hpartC := eq_C_of_vars_eq_nil (primPart d) hconst
      rw [hpartC, C_mul_C] at hdrec
      rw [← hdrec]
      exact isConst_C _
  · intro hp
    refine ⟨?_, ?_⟩
    · intro hq0
      apply hp.1
      rw [← content_mul_primPart p, hq0, MvPoly.mul_zero]
    · intro d hd
      apply hp.2 d
      rcases hd with ⟨a, ha⟩
      refine ⟨C (content p) * a, ?_⟩
      calc
        p = C (content p) * primPart p := (content_mul_primPart p).symm
        _ = C (content p) * (a * (d * d)) :=
          congrArg (fun q => C (content p) * q) ha
        _ = (C (content p) * a) * (d * d) :=
          (MvPoly.mul_assoc ..).symm

omit [LawfulBezoutOps R] [GcdProducer R] in
theorem isConst_of_unit [IsMonomialOrder cmp]
    (d : MvPoly n R cmp)
    (hd : polyIsUnit d = true) : IsConst d := by
  rcases (polyIsUnit_iff d).mp hd with ⟨u, hu⟩
  rcases unit_eq_C LawfulGcdOps.one_ne_zero LawfulGcdOps.no_zero_div hu with
    ⟨c, _, hc, _⟩
  rw [hc]
  exact isConst_C c

omit [LawfulBezoutOps R] [GcdProducer R] in
theorem unit_of_const_dvd_primitive [IsMonomialOrder cmp]
    {q d : MvPoly n R cmp} (hq : Primitive q)
    (hdconst : IsConst d) (hdq : d ∣ q) : polyIsUnit d = true := by
  let c := coeff Mono.zero d
  have hdc : d = C c := eq_C_of_vars_eq_nil d hdconst
  rcases hdq with ⟨a, ha⟩
  have hcommon : ∀ x, x ∈ coefficientList q → c ∣ x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨term, hterm, rfl⟩
    rcases term with ⟨m, x⟩
    have hcoeff : coeff m q = x := coeff_eq_of_mem_terms q hterm
    apply (LawfulGcdOps.dvd_iff c x).mpr
    refine ⟨coeff m a, ?_⟩
    calc
      x = coeff m q := hcoeff.symm
      _ = coeff m (a * d) := congrArg (coeff m) ha
      _ = coeff m (C c * a) := by rw [hdc, MvPoly.mul_comm]
      _ = c * coeff m a := coeff_C_mul c a m
  rcases hq c hcommon with ⟨v, hv⟩
  apply (polyIsUnit_iff d).mpr
  refine ⟨C v, ?_⟩
  rw [hdc, C_mul_C, hv]
  rfl

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
theorem derivative_dvd_of_square_dvd (i : Fin n)
    {d q : MvPoly n R cmp} (h : d * d ∣ q) : d ∣ derivative i q := by
  rcases h with ⟨a, ha⟩
  refine ⟨derivative i a * d + a * (derivative i d + derivative i d), ?_⟩
  rw [ha, derivative_mul, derivative_mul]
  grind

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
theorem dvd_add_poly {a b d : MvPoly n R cmp}
    (ha : d ∣ a) (hb : d ∣ b) : d ∣ a + b := by
  rcases ha with ⟨x, hx⟩
  rcases hb with ⟨y, hy⟩
  refine ⟨x + y, ?_⟩
  rw [hx, hy]
  grind

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
private theorem dvd_sub_poly {a b d : MvPoly n R cmp}
    (ha : d ∣ a) (hb : d ∣ b) : d ∣ a - b := by
  rcases ha with ⟨x, hx⟩
  rcases hb with ⟨y, hy⟩
  refine ⟨x - y, ?_⟩
  rw [hx, hy]
  grind

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
theorem dvd_mul_right_poly {a d : MvPoly n R cmp}
    (b : MvPoly n R cmp) (h : d ∣ a) : d ∣ a * b := by
  rcases h with ⟨x, hx⟩
  refine ⟨x * b, ?_⟩
  rw [hx]
  grind

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
theorem dvd_mul_left_poly {a d : MvPoly n R cmp}
    (b : MvPoly n R cmp) (h : d ∣ a) : d ∣ b * a := by
  rw [MvPoly.mul_comm b a]
  exact dvd_mul_right_poly b h

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
private theorem pow_dvd_pow_succ (d : MvPoly n R cmp) (k : Nat) :
    d ^ k ∣ d ^ (k + 1) := by
  refine ⟨d, ?_⟩
  rw [MvPoly.pow_succ, MvPoly.mul_comm]

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
private theorem pow_dvd_derivative_pow (i : Fin n)
    (d : MvPoly n R cmp) :
    ∀ k : Nat, d ^ k ∣ derivative i (d ^ (k + 1)) := by
  intro k
  induction k with
  | zero =>
      simpa only [MvPoly.pow_zero, MvPoly.pow_succ,
        MvPoly.one_mul] using
        (show (1 : MvPoly n R cmp) ∣ derivative i d from
          ⟨derivative i d, (MvPoly.mul_one _).symm⟩)
  | succ k ih =>
      change d ^ (k + 1) ∣ derivative i (d ^ ((k + 1) + 1))
      rw [show d ^ ((k + 1) + 1) = d ^ (k + 1) * d from
        MvPoly.pow_succ d (k + 1)]
      rw [derivative_mul]
      apply dvd_add_poly
      · rcases ih with ⟨x, hx⟩
        refine ⟨x, ?_⟩
        calc
          derivative i (d ^ (k + 1)) * d = (x * d ^ k) * d := by rw [hx]
          _ = x * d ^ (k + 1) := by rw [MvPoly.pow_succ]; grind
      · refine ⟨derivative i d, ?_⟩
        grind

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
private theorem pow_succ_dvd_mul_derivative (i : Fin n)
    {d a : MvPoly n R cmp} (h : d ∣ a * derivative i d) :
    ∀ k : Nat, d ^ (k + 1) ∣
      a * derivative i (d ^ (k + 1)) := by
  intro k
  induction k with
  | zero =>
      simpa only [MvPoly.pow_succ, MvPoly.pow_zero,
        MvPoly.one_mul] using h
  | succ k ih =>
      rw [show d ^ (k + 1 + 1) = d ^ (k + 1) * d from
        MvPoly.pow_succ d (k + 1), derivative_mul]
      rw [MvPoly.mul_add]
      apply dvd_add_poly
      · rcases ih with ⟨x, hx⟩
        refine ⟨x, ?_⟩
        calc
          a * (derivative i (d ^ (k + 1)) * d) =
              (a * derivative i (d ^ (k + 1))) * d := by grind
          _ = (x * d ^ (k + 1)) * d := by rw [hx]
          _ = x * (d ^ (k + 1) * d) := by grind
      · rcases h with ⟨x, hx⟩
        refine ⟨x, ?_⟩
        calc
          a * (d ^ (k + 1) * derivative i d) =
              d ^ (k + 1) * (a * derivative i d) := by grind
          _ = d ^ (k + 1) * (x * d) := by rw [hx]
          _ = x * (d ^ (k + 1) * d) := by grind

omit [LawfulBezoutOps R] [GcdProducer R] in
private theorem derivative_ne_zero_of_mem_vars [NatNoZero R]
    {m : Nat} {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    (i : Fin (m + 1)) (p : MvPoly (m + 1) R order)
    (hi : i ∈ p.vars) : derivative i p ≠ 0 := by
  intro hderiv
  have hterm : ∀ term ∈ p.termsList,
      Mono.degreeOf i term.1 = 0 := by
    intro term hterm
    rcases term with ⟨monomial, coefficient⟩
    have hcoeff : coeff monomial p = coefficient :=
      coeff_eq_of_mem_terms p hterm
    by_cases hdegree : Mono.degreeOf i monomial = 0
    · exact hdegree
    · have hsucc : Mono.succAt i (predAt i monomial) = monomial :=
        ((predAt_eq_iff i (predAt i monomial) monomial hdegree).mp rfl).symm
      have hzero := congrArg (coeff (predAt i monomial)) hderiv
      rw [coeff_derivative, coeff_zero, hsucc, hcoeff] at hzero
      have hcast :
          ((Mono.degreeOf i (predAt i monomial) + 1 : Nat) : R) ≠ 0 :=
        NatNoZero.natCast_ne_zero _ (by omega)
      have hcoefficient : coefficient ≠ 0 := by
        have hmonomial : monomial ∈ p.monomials :=
          List.mem_map.mpr ⟨(monomial, coefficient), hterm, rfl⟩
        simpa only [hcoeff] using (mem_monomials_iff monomial p).mp hmonomial
      rcases LawfulGcdOps.no_zero_div
          (((Mono.degreeOf i (predAt i monomial) + 1 : Nat) : R))
          coefficient hzero with hzeroCast | hzeroCoeff
      · exact False.elim (hcast hzeroCast)
      · exact False.elim (hcoefficient hzeroCoeff)
  have hdegree : degreeOf i p = 0 := by
    rw [degreeOf_eq]
    unfold foldTerms
    rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
    have fold_zero : ∀ (terms : List (Mono (m + 1) × R)),
        (∀ term ∈ terms, Mono.degreeOf i term.1 = 0) →
          terms.foldl
            (fun degree term => max degree (Mono.degreeOf i term.1)) 0 = 0 := by
      intro terms hall
      induction terms with
      | nil => rfl
      | cons head tail ih =>
          rw [List.foldl_cons, hall head (by simp), Nat.max_zero]
          apply ih
          intro term ht
          exact hall term (by simp [ht])
    exact fold_zero p.termsList hterm
  exact (mem_vars_iff i p).mp hi hdegree

omit [LawfulBezoutOps R] [GcdProducer R] in
private theorem view_size_gt_one_of_mem_vars [NatNoZero R]
    {m : Nat} {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    (i : Fin (m + 1)) (p : MvPoly (m + 1) R order)
    (hi : i ∈ p.vars) : 1 < (toUnivariate i Mono.lex p).size := by
  have hderiv : derivative i p ≠ 0 :=
    derivative_ne_zero_of_mem_vars i p hi
  have hviewDeriv : toUnivariate i Mono.lex (derivative i p) ≠ 0 := by
    intro hzero
    apply hderiv
    calc
      derivative i p = ofUnivariate i Mono.lex
          (toUnivariate i Mono.lex (derivative i p)) :=
        (ofUnivariate_toUnivariate i _).symm
      _ = 0 := by rw [hzero]; rfl
  have hsizePos :
      0 < (toUnivariate i Mono.lex (derivative i p)).size :=
    Nat.pos_of_ne_zero (fun h => hviewDeriv ((DensePoly.size_eq_zero_iff _).mp h))
  have hdrop := DensePoly.size_derivative_le (toUnivariate i Mono.lex p)
  rw [← toUnivariate_derivative] at hdrop
  omega

omit [LawfulBezoutOps R] [GcdProducer R] in
theorem view_pow_size_lower [NatNoZero R]
    {m : Nat} {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    (i : Fin (m + 1)) (p : MvPoly (m + 1) R order)
    (hi : i ∈ p.vars) :
    ∀ k : Nat, k + 2 ≤
      (toUnivariate i Mono.lex (p ^ (k + 1))).size := by
  intro k
  have hpSize : 1 < (toUnivariate i Mono.lex p).size :=
    view_size_gt_one_of_mem_vars i p hi
  induction k with
  | zero =>
      simpa only [MvPoly.pow_succ, MvPoly.pow_zero, MvPoly.one_mul] using
        (show 2 ≤ (toUnivariate i Mono.lex p).size by omega)
  | succ k ih =>
      rw [show p ^ (k + 1 + 1) = p ^ (k + 1) * p from
        MvPoly.pow_succ p (k + 1), toUnivariate_mul]
      let left := toUnivariate i Mono.lex (p ^ (k + 1))
      let right := toUnivariate i Mono.lex p
      have hleftPos : 0 < left.size := by
        change 0 < (toUnivariate i Mono.lex (p ^ (k + 1))).size
        omega
      have hrightPos : 0 < right.size := by
        change 0 < (toUnivariate i Mono.lex p).size
        omega
      have htop : left.leadingCoeff * right.leadingCoeff ≠
          (0 : MvPoly m R Mono.lex) := by
        intro hzero
        rcases GcdDomainLaws.no_zero_div
            left.leadingCoeff right.leadingCoeff hzero with hl | hr
        · exact (DensePoly.leadingCoeff_ne_zero_of_pos_size left hleftPos) hl
        · exact (DensePoly.leadingCoeff_ne_zero_of_pos_size right hrightPos) hr
      have hsize := DensePoly.size_mul_of_top_ne
        left right hleftPos hrightPos htop
      change k + 1 + 2 ≤ (left * right).size
      rw [hsize]
      change k + 2 ≤ left.size at ih
      change 1 < right.size at hpSize
      omega

omit [LawfulBezoutOps R] [GcdProducer R] in
theorem isConst_of_all_powers_dvd [NatNoZero R]
    {p d : MvPoly n R cmp} (hp : p ≠ 0)
    (hall : ∀ k : Nat, d ^ (k + 1) ∣ p) : IsConst d := by
  cases n with
  | zero =>
      unfold IsConst
      rw [vars_eq]
      simp [Mono.support]
  | succ m =>
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro i hi
      have hlower := view_pow_size_lower i d hi
        (toUnivariate i Mono.lex p).size
      rcases hall (toUnivariate i Mono.lex p).size with ⟨q, hq⟩
      have hviewP : toUnivariate i Mono.lex p ≠ 0 := by
        intro hzero
        apply hp
        calc
          p = ofUnivariate i Mono.lex (toUnivariate i Mono.lex p) :=
            (ofUnivariate_toUnivariate i p).symm
          _ = 0 := by rw [hzero]; rfl
      have hpowView :
          toUnivariate i Mono.lex
              (d ^ ((toUnivariate i Mono.lex p).size + 1)) ≠ 0 := by
        intro hzero
        have hsize := congrArg DensePoly.size hzero
        rw [DensePoly.size_zero] at hsize
        omega
      have hqView : toUnivariate i Mono.lex q ≠ 0 := by
        intro hzero
        apply hviewP
        rw [hq, toUnivariate_mul, hzero, DensePoly.zero_mul]
      have hqPos : 0 < (toUnivariate i Mono.lex q).size :=
        Nat.pos_of_ne_zero
          (fun h => hqView ((DensePoly.size_eq_zero_iff _).mp h))
      have hpowPos : 0 < (toUnivariate i Mono.lex
          (d ^ ((toUnivariate i Mono.lex p).size + 1))).size :=
        Nat.pos_of_ne_zero
          (fun h => hpowView ((DensePoly.size_eq_zero_iff _).mp h))
      have htop :
          (toUnivariate i Mono.lex q).leadingCoeff *
              (toUnivariate i Mono.lex
                (d ^ ((toUnivariate i Mono.lex p).size + 1))).leadingCoeff ≠
            (0 : MvPoly m R Mono.lex) := by
        intro hzero
        rcases GcdDomainLaws.no_zero_div _ _ hzero with hl | hr
        · exact (DensePoly.leadingCoeff_ne_zero_of_pos_size _ hqPos) hl
        · exact (DensePoly.leadingCoeff_ne_zero_of_pos_size _ hpowPos) hr
      have hproduct := DensePoly.size_mul_of_top_ne _ _ hqPos hpowPos htop
      have hviewEq := congrArg (fun f => (toUnivariate i Mono.lex f).size) hq
      rw [toUnivariate_mul, hproduct] at hviewEq
      omega

@[simp] theorem gcdList_derivatives_zero [IsMonomialOrder cmp] :
    gcdList ((0 : MvPoly n R cmp) :: derivatives 0) = 0 := by
  unfold gcdList derivatives
  simp only [mvDerivative_zero, List.foldl_cons, gcd_zero_zero]
  have fold_zero : ∀ (xs : List (MvPoly n R cmp)),
      (∀ x ∈ xs, x = 0) → xs.foldl gcd 0 = 0 := by
    intro xs hall
    induction xs with
    | nil => rfl
    | cons head tail ih =>
        rw [List.foldl_cons, hall head (by simp), gcd_zero_zero]
        apply ih
        intro x hx
        exact hall x (by simp [hx])
  apply fold_zero
  intro x hx
  rcases List.mem_map.mp hx with ⟨i, _, rfl⟩
  exact mvDerivative_zero i

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
/-- Interior binomial coefficients vanish in a ring of prime
characteristic. -/
private theorem natCast_choose_prime_eq_zero {S : Type u}
    [Lean.Grind.CommRing S] {prime : Nat} (hprime : Hex.Nat.Prime prime)
    (hchar : (prime : S) = 0) {k : Nat} (hk0 : 0 < k)
    (hkp : k < prime) : (Hex.Nat.choose prime k : S) = 0 := by
  rcases Hex.Nat.choose_prime_dvd hprime hk0 hkp with ⟨a, ha⟩
  have hcast := congrArg (fun m : Nat => (m : S)) ha
  rw [Lean.Grind.Semiring.natCast_mul, hchar,
    Lean.Grind.Semiring.zero_mul] at hcast
  exact hcast

private theorem prime_dvd_of_natCast_eq_zero {S : Type u}
    [Lean.Grind.CommRing S] {prime value : Nat}
    (hprime : Hex.Nat.Prime prime) (hchar : (prime : S) = 0)
    (hone : (1 : S) ≠ 0) (hvalue : (value : S) = 0) :
    prime ∣ value := by
  by_cases hdiv : prime ∣ value
  · exact hdiv
  exfalso
  let hnot := hdiv
  have hcop := Hex.Nat.Prime.coprime_of_not_dvd hprime hnot
  have hbez := HexArith.extGcd_bezout_gcd prime value
  rw [show Nat.gcd prime value = 1 from hcop] at hbez
  have hcast := congrArg (fun z : Int => (z : S)) hbez
  simp only [Lean.Grind.Ring.intCast_add, Lean.Grind.Ring.intCast_mul,
    Lean.Grind.Ring.intCast_natCast, Lean.Grind.Ring.intCast_one,
    hchar, hvalue, Lean.Grind.Semiring.mul_zero,
    Lean.Grind.AddCommMonoid.add_zero] at hcast
  apply hone
  calc
    (1 : S) = ((1 : Nat) : S) := Lean.Grind.Semiring.natCast_one.symm
    _ = 0 := hcast.symm

private def sqfPow {S : Type u} [One S] [Mul S] (a : S) : Nat → S
  | 0 => 1
  | k + 1 => sqfPow a k * a

private theorem sqfPow_add {S : Type u} [Lean.Grind.CommRing S]
    (a : S) (j k : Nat) : sqfPow a (j + k) = sqfPow a j * sqfPow a k := by
  induction k with
  | zero => rw [Nat.add_zero, sqfPow, Lean.Grind.Semiring.mul_one]
  | succ k ih =>
      rw [Nat.add_succ, sqfPow, ih, sqfPow,
        Lean.Grind.Semiring.mul_assoc]

private theorem sqfPow_succ_left {S : Type u} [Lean.Grind.CommRing S]
    (a : S) (k : Nat) : sqfPow a (k + 1) = a * sqfPow a k := by
  rw [sqfPow, Lean.Grind.CommSemiring.mul_comm]

private theorem sqfPow_zero {S : Type u} [Lean.Grind.CommRing S]
    (a : S) : sqfPow a 0 = 1 := rfl

private def sqfBinomTerm {S : Type u} [Lean.Grind.CommRing S]
    (a b : S) (degree k : Nat) : S :=
  (Hex.Nat.choose degree k : S) *
    (sqfPow a (degree - k) * sqfPow b k)

private def sqfBinomSum {S : Type u} [Lean.Grind.CommRing S]
    (a b : S) (degree : Nat) : Nat → S
  | 0 => 0
  | k + 1 => sqfBinomSum a b degree k + sqfBinomTerm a b degree k

private theorem sqfBinomTerm_succ_zero {S : Type u}
    [Lean.Grind.CommRing S] (a b : S) (degree : Nat) :
    sqfBinomTerm a b (degree + 1) 0 = a * sqfBinomTerm a b degree 0 := by
  unfold sqfBinomTerm
  simp only [Hex.Nat.choose_zero_right, Lean.Grind.Semiring.natCast_one,
    Nat.sub_zero, sqfPow_zero, Lean.Grind.Semiring.mul_one,
    Lean.Grind.Semiring.one_mul, sqfPow_succ_left]

private theorem sqfBinomTerm_succ_succ {S : Type u}
    [Lean.Grind.CommRing S] (a b : S) {degree k : Nat} (hk : k ≤ degree) :
    sqfBinomTerm a b (degree + 1) (k + 1) =
      a * sqfBinomTerm a b degree (k + 1) +
        b * sqfBinomTerm a b degree k := by
  unfold sqfBinomTerm
  rw [Hex.Nat.choose_succ_succ]
  rw [Lean.Grind.Semiring.natCast_add]
  by_cases htop : k = degree
  · subst k
    rw [Hex.Nat.choose_self degree,
      Hex.Nat.choose_eq_zero_of_lt (by omega)]
    simp only [Lean.Grind.Semiring.natCast_zero,
      Lean.Grind.Semiring.natCast_one]
    have hsub1 : degree + 1 - (degree + 1) = 0 := by omega
    have hsub2 : degree - (degree + 1) = 0 := by omega
    have hsub3 : degree - degree = 0 := by omega
    rw [hsub1, hsub2, hsub3, sqfPow_zero, sqfPow_succ_left]
    grind
  · have hlt : k < degree := by omega
    have hsub1 : degree + 1 - (k + 1) = degree - k := by omega
    have hsub2 : degree - k = degree - (k + 1) + 1 := by omega
    rw [hsub1, hsub2, sqfPow_succ_left, sqfPow_succ_left]
    grind

private theorem sqfBinomSum_succ_row {S : Type u}
    [Lean.Grind.CommRing S] (a b : S) (degree count : Nat)
    (hcount : count ≤ degree + 1) :
    sqfBinomSum a b (degree + 1) (count + 1) =
      a * sqfBinomSum a b degree (count + 1) +
        b * sqfBinomSum a b degree count := by
  induction count with
  | zero =>
      change 0 + sqfBinomTerm a b (degree + 1) 0 =
        a * (0 + sqfBinomTerm a b degree 0) + b * 0
      rw [sqfBinomTerm_succ_zero]
      grind
  | succ count ih =>
      rw [sqfBinomSum, ih (by omega), sqfBinomSum, sqfBinomSum,
        sqfBinomTerm_succ_succ a b (by omega)]
      have hsum : sqfBinomSum a b degree (count + 1) =
          sqfBinomSum a b degree count + sqfBinomTerm a b degree count := rfl
      rw [hsum]
      grind

private theorem sqfBinomSum_top_succ {S : Type u}
    [Lean.Grind.CommRing S] (a b : S) (degree : Nat) :
    sqfBinomSum a b degree (degree + 1 + 1) =
      sqfBinomSum a b degree (degree + 1) := by
  rw [sqfBinomSum]
  have htop : sqfBinomTerm a b degree (degree + 1) = 0 := by
    unfold sqfBinomTerm
    rw [Hex.Nat.choose_eq_zero_of_lt (by omega),
      Lean.Grind.Semiring.natCast_zero, Lean.Grind.Semiring.zero_mul]
  rw [htop]
  exact Lean.Grind.AddCommMonoid.add_zero _

private theorem sqfPow_add_binom {S : Type u} [Lean.Grind.CommRing S]
    (a b : S) (degree : Nat) :
    sqfPow (a + b) degree = sqfBinomSum a b degree (degree + 1) := by
  induction degree with
  | zero =>
      simp only [sqfPow, sqfBinomSum, sqfBinomTerm,
        Hex.Nat.choose_zero_right, Lean.Grind.Semiring.natCast_one,
        Nat.zero_sub, Lean.Grind.Semiring.one_mul]
      grind
  | succ degree ih =>
      rw [sqfPow_succ_left, ih,
        sqfBinomSum_succ_row a b degree (degree + 1) (by omega),
        sqfBinomSum_top_succ a b degree]
      grind

private theorem sqfBinomTerm_prime_zero {S : Type u}
    [Lean.Grind.CommRing S] (a b : S) (prime : Nat) :
    sqfBinomTerm a b prime 0 = sqfPow a prime := by
  unfold sqfBinomTerm
  rw [Hex.Nat.choose_zero_right, Lean.Grind.Semiring.natCast_one,
    Nat.sub_zero, sqfPow_zero]
  grind

private theorem sqfBinomTerm_prime_top {S : Type u}
    [Lean.Grind.CommRing S] (a b : S) (prime : Nat) :
    sqfBinomTerm a b prime prime = sqfPow b prime := by
  unfold sqfBinomTerm
  rw [Hex.Nat.choose_self, Lean.Grind.Semiring.natCast_one,
    Nat.sub_self, sqfPow_zero]
  grind

private theorem sqfBinomTerm_prime_middle {S : Type u}
    [Lean.Grind.CommRing S] {prime : Nat} (hprime : Hex.Nat.Prime prime)
    (hchar : (prime : S) = 0) (a b : S) {k : Nat}
    (hk0 : 0 < k) (hkp : k < prime) :
    sqfBinomTerm a b prime k = 0 := by
  unfold sqfBinomTerm
  rw [natCast_choose_prime_eq_zero hprime hchar hk0 hkp]
  exact Lean.Grind.Semiring.zero_mul _

private theorem sqfBinomSum_prime_middle {S : Type u}
    [Lean.Grind.CommRing S] {prime : Nat} (hprime : Hex.Nat.Prime prime)
    (hchar : (prime : S) = 0) (a b : S) {count : Nat}
    (hcount : count < prime) :
    sqfBinomSum a b prime (count + 1) = sqfPow a prime := by
  induction count with
  | zero =>
      change 0 + sqfBinomTerm a b prime 0 = sqfPow a prime
      rw [sqfBinomTerm_prime_zero]
      grind
  | succ count ih =>
      rw [sqfBinomSum, ih (by omega),
        sqfBinomTerm_prime_middle hprime hchar a b
          (by omega : 0 < count + 1) (by omega)]
      grind

private theorem sqfPow_add_prime {S : Type u} [Lean.Grind.CommRing S]
    {prime : Nat} (hprime : Hex.Nat.Prime prime)
    (hchar : (prime : S) = 0) (a b : S) :
    sqfPow (a + b) prime = sqfPow a prime + sqfPow b prime := by
  have hprimePos : 0 < prime := Hex.Nat.Prime.pos hprime
  rw [sqfPow_add_binom, sqfBinomSum]
  have hmiddle : sqfBinomSum a b prime prime = sqfPow a prime := by
    have h := sqfBinomSum_prime_middle hprime hchar a b
      (count := prime - 1) (by omega)
    simpa [Nat.sub_add_cancel hprimePos] using h
  rw [hmiddle, sqfBinomTerm_prime_top]

private theorem sqfPow_eq_pow {S : Type u} [Lean.Grind.CommRing S]
    (a : S) (k : Nat) : sqfPow a k = a ^ k := by
  induction k with
  | zero => rw [sqfPow, Lean.Grind.Semiring.pow_zero]
  | succ k ih =>
      rw [sqfPow, ih, Lean.Grind.Semiring.pow_succ]

private theorem pow_add_prime {S : Type u} [Lean.Grind.CommRing S]
    {prime : Nat} (hprime : Hex.Nat.Prime prime)
    (hchar : (prime : S) = 0) (a b : S) :
    (a + b) ^ prime = a ^ prime + b ^ prime := by
  rw [← sqfPow_eq_pow, ← sqfPow_eq_pow, ← sqfPow_eq_pow]
  exact sqfPow_add_prime hprime hchar a b

private theorem mvMonomial_pow {S : Type u} [Lean.Grind.CommRing S]
    [DecidableEq S] [BEq S] [LawfulBEq S]
    (m : Mono n) (c : S) (k : Nat) :
    (monomial m c : MvPoly n S cmp) ^ k =
      monomial (Mono.scale k m) (c ^ k) := by
  induction k with
  | zero =>
      rw [Lean.Grind.Semiring.pow_zero, Lean.Grind.Semiring.pow_zero,
        Mono.zero_scale]
      rfl
  | succ k ih =>
      rw [MvPoly.pow_succ, ih, monomial_mul_monomial,
        Lean.Grind.Semiring.pow_succ]
      congr 1
      calc
        Mono.mul (Mono.scale k m) m =
            Mono.mul (Mono.scale k m) (Mono.scale 1 m) := by
          rw [Mono.one_scale]
        _ = Mono.scale (k + 1) m := (Mono.add_scale k 1 m).symm

private def monoDiv (prime : Nat) (m : Mono n) : Mono n :=
  Hex.Vector.ofFn' fun i => m[i] / prime

@[simp] private theorem get_monoDiv (prime : Nat) (m : Mono n)
    (i : Fin n) : (monoDiv prime m)[i] = m[i] / prime := by
  unfold monoDiv
  change (Hex.Vector.ofFn' fun i : Fin n => m[i] / prime)[i.val] =
    m[i] / prime
  rw [Hex.Vector.getElem_ofFn' _ i.val i.isLt]

private theorem scale_monoDiv {prime : Nat} (hprime : 0 < prime)
    (m : Mono n) (hdiv : ∀ i : Fin n, prime ∣ m[i]) :
    Mono.scale prime (monoDiv prime m) = m := by
  apply Vector.ext
  intro i hi
  let j : Fin n := ⟨i, hi⟩
  have hgoal :
      (Mono.scale prime (monoDiv prime m))[j] = m[j] := by
    rw [Mono.getElem_scale, get_monoDiv, Nat.mul_comm]
    exact Nat.div_mul_cancel (hdiv j)
  exact hgoal

private def termSum {S : Type u} [Lean.Grind.CommRing S]
    [DecidableEq S] [BEq S] [LawfulBEq S]
    (terms : List (Mono n × S)) : MvPoly n S cmp :=
  match terms with
  | [] => 0
  | term :: rest => monomial term.1 term.2 + termSum rest

private theorem foldTerms_eq_add_sum {S : Type u} [Lean.Grind.CommRing S]
    [DecidableEq S] [BEq S] [LawfulBEq S]
    (terms : List (Mono n × S)) (acc : MvPoly n S cmp) :
    terms.foldl (fun p term => addMonomial p term.1 term.2) acc =
      acc + termSum terms := by
  induction terms generalizing acc with
  | nil => exact rfl
  | cons term rest ih =>
      rw [List.foldl_cons, ih, addMonomial_eq, termSum, add_assoc]

private theorem termSum_termsList {S : Type u} [Lean.Grind.CommRing S]
    [DecidableEq S] [BEq S] [LawfulBEq S]
    (p : MvPoly n S cmp) : termSum p.termsList = p := by
  calc
    termSum p.termsList = ofTerms p.termsList := by
      unfold ofTerms
      rw [foldTerms_eq_add_sum, zero_add]
    _ = p := by
      apply MvPoly.ext
      intro m
      rw [coeff_ofTerms, coeff_terms]

private theorem termSum_map_add_prime {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [BEq S] [LawfulBEq S]
    {prime : Nat} (hprime : Hex.Nat.Prime prime)
    (hchar : (prime : S) = 0) (terms : List (Mono n × S)) :
    (termSum terms : MvPoly n S cmp) ^ prime =
      termSum (terms.map fun term =>
        (Mono.scale prime term.1, term.2 ^ prime)) := by
  have hcharPoly :
      (prime : MvPoly n S cmp) = (0 : MvPoly n S cmp) := by
    apply MvPoly.ext
    intro m
    rw [coeff_natCast, coeff_zero]
    by_cases hm : m = Mono.zero
    · rw [ite_eq_left hm, hchar]
    · rw [ite_eq_right hm]
  induction terms with
  | nil =>
      change (0 : MvPoly n S cmp) ^ prime = 0
      have hprimePos := Hex.Nat.Prime.pos hprime
      cases prime with
      | zero => contradiction
      | succ k => rw [MvPoly.pow_succ, MvPoly.mul_zero]
  | cons term rest ih =>
      change (monomial term.1 term.2 + termSum rest) ^ prime =
        monomial (Mono.scale prime term.1) (term.2 ^ prime) +
          termSum (rest.map fun term =>
            (Mono.scale prime term.1, term.2 ^ prime))
      rw [pow_add_prime hprime hcharPoly, mvMonomial_pow, ih]

private noncomputable def perfectCoeffRoot {S : Type u}
    [Lean.Grind.CommRing S] {prime : Nat}
    (hperfect : ∀ a : S, ∃ b : S, b ^ prime = a) (a : S) : S :=
  Classical.choose (hperfect a)

private theorem perfectCoeffRoot_pow {S : Type u}
    [Lean.Grind.CommRing S] {prime : Nat}
    (hperfect : ∀ a : S, ∃ b : S, b ^ prime = a) (a : S) :
    (perfectCoeffRoot hperfect a) ^ prime = a :=
  Classical.choose_spec (hperfect a)

private noncomputable def perfectPolyRoot
    [Div R] [ExactDivLaws R] [Hex.Fraction.NonzeroOne R]
    {prime : Nat}
    (hperfect : ∀ a : Hex.Fraction R,
      ∃ b : Hex.Fraction R, b ^ prime = a)
    (p : MvPoly n R cmp) : MvPoly n (Hex.Fraction R) cmp :=
  termSum (p.termsList.map fun term =>
    (monoDiv prime term.1,
      perfectCoeffRoot hperfect (Hex.Fraction.ofCoeff term.2)))

private theorem fractionMap_monomial
    [Div R] [ExactDivLaws R] [Hex.Fraction.NonzeroOne R]
    (m : Mono n) (c : R) :
    fractionMap (monomial m c : MvPoly n R cmp) =
      (monomial m (Hex.Fraction.ofCoeff c) :
        MvPoly n (Hex.Fraction R) cmp) := by
  apply MvPoly.ext
  intro k
  rw [fractionMap, coeff_mapCoeffs Hex.Fraction.ofCoeff_zero,
    coeff_monomial, coeff_monomial]
  by_cases hkm : k = m
  · rw [ite_eq_left hkm, ite_eq_left hkm]
  · rw [ite_eq_right hkm, ite_eq_right hkm]
    exact (Hex.Fraction.ofCoeff_eq_zero_iff _).mpr rfl

private theorem fractionMap_termSum
    [Div R] [ExactDivLaws R] [Hex.Fraction.NonzeroOne R]
    (terms : List (Mono n × R)) :
    fractionMap (termSum terms : MvPoly n R cmp) =
      termSum (terms.map fun term =>
        (term.1, Hex.Fraction.ofCoeff term.2)) := by
  induction terms with
  | nil =>
      change fractionMap (0 : MvPoly n R cmp) =
        (0 : MvPoly n (Hex.Fraction R) cmp)
      exact fractionMap_zero
  | cons term rest ih =>
      change fractionMap
          (monomial term.1 term.2 + termSum rest) =
        monomial term.1 (Hex.Fraction.ofCoeff term.2) +
          termSum (rest.map fun term =>
            (term.1, Hex.Fraction.ofCoeff term.2))
      rw [fractionMap_add, fractionMap_monomial, ih]

private theorem exponent_dvd_of_derivatives_zero
    [Div R] [ExactDivLaws R] [Hex.Fraction.NonzeroOne R]
    {prime : Nat} (hprime : Hex.Nat.Prime prime)
    (hchar : (prime : Hex.Fraction R) = 0)
    (p : MvPoly n R cmp) (hderiv : ∀ i, derivative i p = 0) :
    ∀ term ∈ p.termsList, ∀ i : Fin n, prime ∣ term.1[i] := by
  intro term hterm i
  rcases term with ⟨m, c⟩
  by_cases he : m[i] = 0
  · rw [he]
    exact Nat.dvd_zero prime
  have hsucc : Mono.succAt i (predAt i m) = m :=
    ((predAt_eq_iff i (predAt i m) m he).mp rfl).symm
  have hdegree := congrArg (Mono.degreeOf i) hsucc
  rw [degreeOf_succAt] at hdegree
  have hcoeff := congrArg (coeff (predAt i m)) (hderiv i)
  rw [coeff_derivative, coeff_zero, hsucc] at hcoeff
  have hc : c ≠ 0 := by
    intro hzero
    subst c
    have hget :=
      (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some).mp hterm
    exact p.nonzeroInternal m hget
  have hcoeffTerm : coeff m p = c := coeff_eq_of_mem_terms p hterm
  rw [hcoeffTerm] at hcoeff
  change ((Mono.degreeOf i (predAt i m) + 1 : Nat) : R) * c = 0 at hcoeff
  rw [hdegree] at hcoeff
  have hcastR : ((m[i] : Nat) : R) = 0 := by
    rcases LawfulGcdOps.no_zero_div ((m[i] : Nat) : R) c hcoeff with
      hzero | hzero
    · exact hzero
    · exact False.elim (hc hzero)
  have hcastF : ((m[i] : Nat) : Hex.Fraction R) = 0 := by
    change Hex.Fraction.ofCoeff ((m[i] : Nat) : R) = 0
    exact (Hex.Fraction.ofCoeff_eq_zero_iff _).mpr hcastR
  exact prime_dvd_of_natCast_eq_zero hprime hchar
    (fun h => Lean.Grind.Field.zero_ne_one h.symm) hcastF

private theorem perfectPolyRoot_pow
    [Div R] [ExactDivLaws R] [Hex.Fraction.NonzeroOne R]
    {prime : Nat} (hprime : Hex.Nat.Prime prime)
    (hchar : (prime : Hex.Fraction R) = 0)
    (hperfect : ∀ a : Hex.Fraction R,
      ∃ b : Hex.Fraction R, b ^ prime = a)
    (p : MvPoly n R cmp) (hderiv : ∀ i, derivative i p = 0) :
    (perfectPolyRoot hperfect p) ^ prime = fractionMap p := by
  let rootTerms := p.termsList.map fun term =>
    (monoDiv prime term.1,
      perfectCoeffRoot hperfect (Hex.Fraction.ofCoeff term.2))
  have hpowered :
      rootTerms.map (fun term =>
        (Mono.scale prime term.1, term.2 ^ prime)) =
        p.termsList.map fun term =>
          (term.1, Hex.Fraction.ofCoeff term.2) := by
    unfold rootTerms
    rw [List.map_map]
    apply List.map_congr_left
    intro term hterm
    apply Prod.ext
    · exact scale_monoDiv (Hex.Nat.Prime.pos hprime) term.1
        (exponent_dvd_of_derivatives_zero hprime hchar p hderiv term hterm)
    · exact perfectCoeffRoot_pow hperfect _
  calc
    (perfectPolyRoot hperfect p) ^ prime =
        termSum (rootTerms.map fun term =>
          (Mono.scale prime term.1, term.2 ^ prime)) := by
      unfold perfectPolyRoot
      exact termSum_map_add_prime hprime hchar rootTerms
    _ = termSum (p.termsList.map fun term =>
          (term.1, Hex.Fraction.ofCoeff term.2)) := by rw [hpowered]
    _ = fractionMap (termSum p.termsList : MvPoly n R cmp) :=
      (fractionMap_termSum p.termsList).symm
    _ = fractionMap p := by rw [termSum_termsList]

omit [LawfulBezoutOps R] [GcdProducer R] in
theorem content_eq_one_of_primitive
    {p : MvPoly n R cmp} (hprimitive : Primitive p) : content p = 1 := by
  have hcommon : ∀ c, c ∈ coefficientList p → content p ∣ c := by
    intro c hc
    rcases List.mem_map.mp hc with ⟨term, hterm, rfl⟩
    rcases term with ⟨m, c⟩
    rw [← coeff_eq_of_mem_terms p hterm]
    exact scalarContent_dvd_coeff p m
  rcases hprimitive (content p) hcommon with ⟨u, hu⟩
  have hunit : GcdOps.isUnit (content p) = true :=
    (LawfulGcdOps.isUnit_iff _).mpr ⟨u, hu⟩
  have hnormalize : normalize (content p) = content p :=
    normalize_scalarContent p
  calc
    content p = normalize (content p) := hnormalize.symm
    _ = 1 := LawfulGcdOps.normalize_unit _ hunit

omit [LawfulBezoutOps R] [GcdProducer R] in
theorem primitive_of_dvd_primitive [IsMonomialOrder cmp]
    {p q : MvPoly n R cmp} (hp : Primitive p) (hqp : q ∣ p) :
    Primitive q := by
  rcases hqp with ⟨a, ha⟩
  intro d hd
  have hdContent : d ∣ content q := by
    apply dvd_scalarContent q d
    intro m
    by_cases hm : m ∈ q.monomials
    · rcases List.mem_map.mp hm with ⟨term, hterm, hmono⟩
      rcases term with ⟨termMono, termCoeff⟩
      simp only at hmono
      subst termMono
      rw [coeff_eq_of_mem_terms q hterm]
      apply hd termCoeff
      exact List.mem_map.mpr ⟨(m, termCoeff), hterm, rfl⟩
    · rw [coeff_eq_zero_of_not_mem m q hm]
      apply (LawfulGcdOps.dvd_iff d 0).mpr
      exact ⟨0, by grind⟩
  rcases (LawfulGcdOps.dvd_iff d (content q)).mp hdContent with ⟨u, hu⟩
  have hcontent := congrArg content ha
  rw [content_mul] at hcontent
  have hpContent : content p = 1 := content_eq_one_of_primitive hp
  refine ⟨content a * u, ?_⟩
  calc
    d * (content a * u) = content a * (u * d) := by grind
    _ = content a * content q := by rw [hu]; grind
    _ = content p := hcontent.symm
    _ = 1 := hpContent

omit [LawfulBezoutOps R] [GcdProducer R] in
private theorem squarefree_of_dvd
    {p q : MvPoly n R cmp} (hp : Squarefree p)
    (hqp : q ∣ p) (hq0 : q ≠ 0) : Squarefree q := by
  refine ⟨hq0, ?_⟩
  intro d hdd
  exact hp.2 d (Hex.dvdTrans hdd hqp)

omit [LawfulBezoutOps R] [GcdProducer R] in
theorem normalized_left_factor [IsMonomialOrder cmp]
    {p q r : MvPoly n R cmp} (hp : polyNormalize p = p)
    (hr : polyNormalize r = r) (hr0 : r ≠ 0)
    (hproduct : q * r = p) : polyNormalize q = q := by
  have hnormProduct := polyNormalize_mul q r
  rw [hproduct, hp, hr] at hnormProduct
  have hzero : (polyNormalize q - q) * r = 0 := by
    calc
      (polyNormalize q - q) * r =
          polyNormalize q * r - q * r := by grind
      _ = p - p := by rw [← hnormProduct, hproduct]
      _ = 0 := by grind
  rcases GcdDomainLaws.no_zero_div (polyNormalize q - q) r hzero with
    hcancel | hzero
  · grind
  · exact False.elim (hr0 hzero)

omit [LawfulBezoutOps R] [GcdProducer R] in
theorem primitive_const_normalized_eq_one [IsMonomialOrder cmp]
    {p : MvPoly n R cmp} (hp : Primitive p)
    (hconst : IsConst p) (hnormalized : polyNormalize p = p) : p = 1 := by
  have hunit := unit_of_const_dvd_primitive hp hconst
    (show p ∣ p from ⟨1, (MvPoly.one_mul p).symm⟩)
  calc
    p = polyNormalize p := hnormalized.symm
    _ = 1 := polyNormalize_unit p hunit

theorem contentIn_one_of_dvd
    {m : Nat} {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    [IsMonomialOrder order]
    (i : Fin (m + 1)) {p d : MvPoly (m + 1) R order}
    (hp : contentIn i Mono.lex p = 1) (hdp : d ∣ p) :
    contentIn i Mono.lex d = 1 := by
  rcases hdp with ⟨a, ha⟩
  have hcontent := congrArg (contentIn i Mono.lex) ha
  rw [contentIn_mul, hp] at hcontent
  have hunit : polyIsUnit (contentIn i Mono.lex d) = true := by
    apply (polyIsUnit_iff _).mpr
    refine ⟨contentIn i Mono.lex a, ?_⟩
    rw [MvPoly.mul_comm]
    exact hcontent.symm
  calc
    contentIn i Mono.lex d =
        polyNormalize (contentIn i Mono.lex d) :=
      (contentIn_normalized i Mono.lex d).symm
    _ = 1 := polyNormalize_unit _ hunit

theorem gcd_quotients [IsMonomialOrder cmp]
    {b d : MvPoly n R cmp} (hb0 : b ≠ 0) :
    let factor := gcd b d
    let nextB := quotient b factor
    let nextC := quotient d factor
    factor ≠ 0 ∧ nextB * factor = b ∧ nextC * factor = d ∧
      (∀ e, e ∣ nextB → e ∣ nextC → polyIsUnit e = true) := by
  let factor := gcd b d
  let nextB := quotient b factor
  let nextC := quotient d factor
  have hfactorB : factor ∣ b := gcd_dvd_left b d
  have hfactorD : factor ∣ d := gcd_dvd_right b d
  have hfactor0 : factor ≠ 0 := by
    intro hzero
    rcases hfactorB with ⟨a, ha⟩
    rw [hzero, MvPoly.mul_zero] at ha
    exact hb0 ha
  have hnextB : nextB * factor = b :=
    quotient_mul_of_dvd hfactor0 hfactorB
  have hnextC : nextC * factor = d :=
    quotient_mul_of_dvd hfactor0 hfactorD
  refine ⟨hfactor0, hnextB, hnextC, ?_⟩
  intro e heB heC
  have hcommonB : factor * e ∣ b := by
    rcases heB with ⟨a, ha⟩
    change nextB = a * e at ha
    refine ⟨a, ?_⟩
    calc
      b = nextB * factor := hnextB.symm
      _ = (a * e) * factor := by rw [ha]
      _ = a * (factor * e) := by grind
  have hcommonD : factor * e ∣ d := by
    rcases heC with ⟨a, ha⟩
    change nextC = a * e at ha
    refine ⟨a, ?_⟩
    calc
      d = nextC * factor := hnextC.symm
      _ = (a * e) * factor := by rw [ha]
      _ = a * (factor * e) := by grind
  rcases dvd_gcd b d (factor * e) hcommonB hcommonD with ⟨a, ha⟩
  have hzero : factor * (1 - a * e) = 0 := by
    calc
      factor * (1 - a * e) = factor - a * (factor * e) := by grind
      _ = 0 := by rw [← ha]; grind
  rcases GcdDomainLaws.no_zero_div factor (1 - a * e) hzero with
    hzero | hcancel
  · exact False.elim (hfactor0 hzero)
  · apply (polyIsUnit_iff e).mpr
    refine ⟨a, ?_⟩
    grind

omit [LawfulBezoutOps R] [GcdProducer R] in
theorem polyNormalize_pow [IsMonomialOrder cmp]
    {p : MvPoly n R cmp} (hp : polyNormalize p = p) :
    ∀ k : Nat, polyNormalize (p ^ k) = p ^ k := by
  intro k
  induction k with
  | zero =>
      rw [MvPoly.pow_zero]
      exact polyNormalize_unit 1 (by
        apply (polyIsUnit_iff (1 : MvPoly n R cmp)).mpr
        exact ⟨1, MvPoly.mul_one 1⟩)
  | succ k ih =>
      rw [MvPoly.pow_succ, polyNormalize_mul, ih, hp]

omit [LawfulBezoutOps R] [GcdProducer R] in
theorem mv_pow_ne_zero {p : MvPoly n R cmp} (hp : p ≠ 0) :
    ∀ k : Nat, p ^ k ≠ 0 := by
  intro k
  induction k with
  | zero =>
      rw [MvPoly.pow_zero]
      exact GcdDomainLaws.one_ne_zero
  | succ k ih =>
      rw [MvPoly.pow_succ]
      intro hzero
      rcases GcdDomainLaws.no_zero_div (p ^ k) p hzero with h | h
      · exact ih h
      · exact hp h

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
theorem mv_one_pow :
    ∀ k : Nat, (1 : MvPoly n R cmp) ^ k = 1 := by
  intro k
  induction k with
  | zero => exact MvPoly.pow_zero 1
  | succ k ih => rw [MvPoly.pow_succ, ih, MvPoly.one_mul]

private theorem primitive_mul_self [IsMonomialOrder cmp]
    {p : MvPoly n R cmp} (hprimitive : Primitive p) :
    Primitive (p * p) := by
  apply primitive_of_scalarContent_one
  change content (p * p) = 1
  rw [content_mul, content_eq_one_of_primitive hprimitive,
    Lean.Grind.Semiring.one_mul]

private theorem primitive_mul [IsMonomialOrder cmp]
    {p q : MvPoly n R cmp} (hp : Primitive p) (hq : Primitive q) :
    Primitive (p * q) := by
  apply primitive_of_scalarContent_one
  change content (p * q) = 1
  rw [content_mul, content_eq_one_of_primitive hp,
    content_eq_one_of_primitive hq, Lean.Grind.Semiring.one_mul]

private theorem isConst_of_fractionMap_unit
    [Div R] [ExactDivLaws R] [Hex.Fraction.NonzeroOne R]
    (p : MvPoly n R cmp)
    (hunit : ∃ u : MvPoly n (Hex.Fraction R) cmp,
      fractionMap p * u = 1) : IsConst p := by
  rcases hunit with ⟨u, hu⟩
  rcases unit_eq_C
      (fun h => Lean.Grind.Field.zero_ne_one h.symm)
      (fun a b hab => by
        by_cases ha : a = 0
        · exact Or.inl ha
        · exact Or.inr (by
            by_cases hb : b = 0
            · exact hb
            · exact False.elim ((ExactDivLaws.mul_ne_zero ha hb) hab)))
      hu with ⟨c, _, hpC, _⟩
  have hpC' : p = C (coeff Mono.zero p) := by
    apply MvPoly.ext
    intro m
    rw [coeff_C]
    by_cases hm : m = Mono.zero
    · rw [ite_eq_left hm]
      subst m
      rfl
    · rw [ite_eq_right hm]
      have hc := congrArg (coeff m) hpC
      rw [fractionMap, coeff_mapCoeffs Hex.Fraction.ofCoeff_zero,
        coeff_C, ite_eq_right hm] at hc
      exact (Hex.Fraction.ofCoeff_eq_zero_iff _).mp hc
  rw [hpC']
  exact isConst_C _

theorem isConst_of_derivatives_zero_perfect
    [IsMonomialOrder cmp]
    [Div R] [ExactDivLaws R] [Hex.Fraction.NonzeroOne R]
    {prime : Nat} (hprime : Hex.Nat.Prime prime)
    (hchar : (prime : Hex.Fraction R) = 0)
    (hperfect : ∀ a : Hex.Fraction R,
      ∃ b : Hex.Fraction R, b ^ prime = a)
    {q g : MvPoly n R cmp} (hsquarefree : Squarefree q)
    (hgq : g ∣ q) (hg0 : g ≠ 0)
    (hderiv : ∀ i, derivative i g = 0) : IsConst g := by
  let H := perfectPolyRoot hperfect g
  have hpow : H ^ prime = fractionMap g :=
    perfectPolyRoot_pow hprime hchar hperfect g hderiv
  have hmapG0 : fractionMap g ≠ 0 := by
    intro hzero
    apply hg0
    apply fractionMap_injective
    rw [fractionMap_zero, hzero]
  have hH0 : H ≠ 0 := by
    intro hzero
    apply hmapG0
    rw [← hpow, hzero]
    have hp : 0 < prime := Hex.Nat.Prime.pos hprime
    cases prime with
    | zero => contradiction
    | succ k => rw [MvPoly.pow_succ, MvPoly.mul_zero]
  rcases fraction_primitive_rep hH0 with
    ⟨h, hprimitive, hHMap, hMapH⟩
  rcases hMapH with ⟨b, hHb⟩
  have hsquareFraction : fractionMap (h * h) ∣ fractionMap g := by
    refine ⟨H ^ (prime - 2) * b * b, ?_⟩
    rw [fractionMap_mul, ← hpow]
    calc
      H ^ prime = H ^ ((prime - 2) + 2) := by
        congr 1
        have := Hex.Nat.Prime.two_le hprime
        omega
      _ = H ^ (prime - 2) * H ^ 2 :=
        Lean.Grind.Semiring.pow_add H (prime - 2) 2
      _ = H ^ (prime - 2) * (H * H) := by
        rw [show 2 = 1 + 1 by omega, Lean.Grind.Semiring.pow_add,
          Lean.Grind.Semiring.pow_one]
      _ = (H ^ (prime - 2) * b * b) *
          (fractionMap h * fractionMap h) := by
        rw [hHb]
        grind
  have hsquareIntegral : h * h ∣ g :=
    primitive_dvd_fraction (primitive_mul_self hprimitive) hsquareFraction
  have hsquareQ : h * h ∣ q := Hex.dvdTrans hsquareIntegral hgq
  have hconst : IsConst h := hsquarefree.2 h hsquareQ
  have hunitH : ∃ u : MvPoly n (Hex.Fraction R) cmp, H * u = 1 := by
    have hunitBase := unit_of_const_dvd_primitive hprimitive hconst
      (show h ∣ h from ⟨1, (MvPoly.one_mul h).symm⟩)
    rcases (polyIsUnit_iff h).mp hunitBase with ⟨v, hv⟩
    have hmapUnit : fractionMap h * fractionMap v = 1 := by
      calc
        fractionMap h * fractionMap v = fractionMap (h * v) :=
          (fractionMap_mul h v).symm
        _ = fractionMap 1 := by rw [hv]
        _ = 1 := fractionMap_one
    rcases hHMap with ⟨a, ha⟩
    refine ⟨a * fractionMap v, ?_⟩
    calc
      H * (a * fractionMap v) = (a * H) * fractionMap v := by grind
      _ = fractionMap h * fractionMap v := by rw [← ha]
      _ = 1 := hmapUnit
  rcases hunitH with ⟨u, hu⟩
  apply isConst_of_fractionMap_unit g
  refine ⟨u ^ prime, ?_⟩
  calc
    fractionMap g * u ^ prime = H ^ prime * u ^ prime := by rw [hpow]
    _ = (H * u) ^ prime :=
      (Lean.Grind.CommSemiring.mul_pow H u prime).symm
    _ = 1 ^ prime := by rw [hu]
    _ = 1 := Lean.Grind.Semiring.one_pow prime

theorem gcdList_unit_iff_squarefree_of_kernel [IsMonomialOrder cmp]
    (q : MvPoly n R cmp) (hprimitive : Primitive q)
    (hkernel : Squarefree q → ∀ g : MvPoly n R cmp, g ∣ q → g ≠ 0 →
      (∀ i, derivative i g = 0) → IsConst g) :
    polyIsUnit (gcdList (q :: derivatives q)) = true ↔ Squarefree q := by
  constructor
  · intro hunit
    refine ⟨?_, ?_⟩
    · intro hq0
      subst q
      rw [gcdList_derivatives_zero] at hunit
      rcases (polyIsUnit_iff (0 : MvPoly n R cmp)).mp hunit with ⟨u, hu⟩
      rw [MvPoly.zero_mul] at hu
      exact LawfulGcdOps.one_ne_zero hu.symm
    · intro d hd
      have hdq : d ∣ q := by
        rcases hd with ⟨a, ha⟩
        refine ⟨a * d, ?_⟩
        calc
          q = a * (d * d) := ha
          _ = (a * d) * d := (MvPoly.mul_assoc ..).symm
      have hdall : ∀ p ∈ q :: derivatives q, d ∣ p := by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hdq
        · rcases List.mem_map.mp hp with ⟨i, hi, rfl⟩
          exact derivative_dvd_of_square_dvd i hd
      have hdg : d ∣ gcdList (q :: derivatives q) := dvd_gcdList hdall
      rcases hdg with ⟨a, ha⟩
      rcases (polyIsUnit_iff _).mp hunit with ⟨u, hu⟩
      apply isConst_of_unit d
      apply (polyIsUnit_iff d).mpr
      refine ⟨a * u, ?_⟩
      calc
        d * (a * u) = (a * d) * u := by grind
        _ = gcdList (q :: derivatives q) * u := by rw [← ha]
        _ = 1 := hu
  · intro hsq
    let g := gcdList (q :: derivatives q)
    have hgq : g ∣ q := gcdList_dvd (by simp)
    by_cases hq0 : q = 0
    · exact False.elim (hsq.1 hq0)
    have hg0 : g ≠ 0 := by
      intro hgzero
      rcases hgq with ⟨a, ha⟩
      rw [hgzero, MvPoly.mul_zero] at ha
      exact hq0 ha
    have hgq' := hgq
    rcases hgq with ⟨e, hqe⟩
    have hcop : ∀ k, k ∣ e → k ∣ g → ∃ u, k * u = 1 := by
      intro k hke hkg
      rcases hke with ⟨a, hea⟩
      rcases hkg with ⟨b, hgb⟩
      have hsqdiv : k * k ∣ q := by
        refine ⟨a * b, ?_⟩
        rw [hqe, hea, hgb]
        grind
      have hkconst := hsq.2 k hsqdiv
      have hkq : k ∣ q := by
        refine ⟨g * a, ?_⟩
        rw [hqe, hea]
        grind
      have hkunit := unit_of_const_dvd_primitive hprimitive hkconst hkq
      exact (polyIsUnit_iff k).mp hkunit
    have hgd : ∀ i, g ∣ derivative i g := by
      intro i
      have hgDerivQ : g ∣ derivative i q := by
        apply gcdList_dvd
        apply List.mem_cons_of_mem
        exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
      rcases hgDerivQ with ⟨x, hx⟩
      have hged : g ∣ derivative i g * e := by
        refine ⟨x - derivative i e, ?_⟩
        rw [hqe, derivative_mul] at hx
        grind
      exact CoprimeCancelLaws.cancel_coprime (derivative i g) e g g hcop hged
        ⟨derivative i g, by grind⟩
    have hgDeriv : ∀ i, derivative i g = 0 :=
      fun i => derivative_eq_zero_of_dvd i g hg0 (hgd i)
    exact unit_of_const_dvd_primitive hprimitive
      (hkernel hsq g hgq' hg0 hgDeriv)
      (gcdList_dvd (by simp))

/-- In characteristic zero, the all-partials gcd criterion is equivalent to
relative squarefreeness for a primitive polynomial. -/
theorem gcdList_unit_iff_squarefree_charZero [IsMonomialOrder cmp]
    [NatNoZero R]
    (q : MvPoly n R cmp) (hprimitive : Primitive q) :
    polyIsUnit (gcdList (q :: derivatives q)) = true ↔ Squarefree q := by
  apply gcdList_unit_iff_squarefree_of_kernel q hprimitive
  intro _ g _ _ hderiv
  exact isConst_of_derivatives_zero g hderiv

theorem powers_dvd_derivative_gcd [IsMonomialOrder cmp]
    {q g r d : MvPoly n R cmp}
    (hg : g = gcdList (q :: derivatives q))
    (hreconstruct : r * g = q)
    (hdr : d ∣ r) (hdderiv : ∀ i, d ∣ derivative i r) :
    ∀ k : Nat, d ^ (k + 1) ∣ g := by
  intro k
  induction k with
  | zero =>
      rw [MvPoly.pow_succ, MvPoly.pow_zero, MvPoly.one_mul]
      rw [hg]
      apply dvd_gcdList
      intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · rw [← hreconstruct]
        exact dvd_mul_right_poly g hdr
      · rcases List.mem_map.mp hp with ⟨i, _, rfl⟩
        rw [← hreconstruct, derivative_mul]
        apply dvd_add_poly
        · exact dvd_mul_right_poly g (hdderiv i)
        · exact dvd_mul_right_poly (derivative i g) hdr
  | succ k ih =>
      rcases hdr with ⟨a, ha⟩
      rcases ih with ⟨b, hb⟩
      have hcofactor : ∀ i, d ∣ a * derivative i d := by
        intro i
        have hfirst : d ∣ derivative i a * d :=
          ⟨derivative i a, by grind⟩
        have hdiff := dvd_sub_poly (hdderiv i) hfirst
        have heq : derivative i r - derivative i a * d =
            a * derivative i d := by
          rw [ha, derivative_mul]
          grind
        rw [heq] at hdiff
        exact hdiff
      have hq : d ^ (k + 1 + 1) ∣ q := by
        refine ⟨a * b, ?_⟩
        calc
          q = r * g := hreconstruct.symm
          _ = (a * d) * (b * d ^ (k + 1)) := by rw [ha, hb]
          _ = (a * b) * (d ^ (k + 1) * d) := by grind
          _ = (a * b) * d ^ (k + 1 + 1) :=
            congrArg (fun x => (a * b) * x)
              (MvPoly.pow_succ d (k + 1)).symm
      have hderivative : ∀ i, d ^ (k + 1 + 1) ∣ derivative i q := by
        intro i
        rw [← hreconstruct, derivative_mul]
        apply dvd_add_poly
        · rcases hdderiv i with ⟨c, hc⟩
          refine ⟨c * b, ?_⟩
          calc
            derivative i r * g = (c * d) * (b * d ^ (k + 1)) := by
              rw [hc, hb]
            _ = (c * b) * (d ^ (k + 1) * d) := by grind
            _ = (c * b) * d ^ (k + 1 + 1) :=
              congrArg (fun x => (c * b) * x)
                (MvPoly.pow_succ d (k + 1)).symm
        · rw [hb, derivative_mul]
          rw [MvPoly.mul_add]
          apply dvd_add_poly
          · refine ⟨a * derivative i b, ?_⟩
            calc
              r * (derivative i b * d ^ (k + 1)) =
                  (a * d) * (derivative i b * d ^ (k + 1)) := by rw [ha]
              _ = (a * derivative i b) * (d ^ (k + 1) * d) := by grind
              _ = (a * derivative i b) * d ^ (k + 1 + 1) :=
                congrArg (fun x => (a * derivative i b) * x)
                  (MvPoly.pow_succ d (k + 1)).symm
          · have hpower := pow_succ_dvd_mul_derivative i (hcofactor i) k
            rcases hpower with ⟨c, hc⟩
            refine ⟨b * c, ?_⟩
            calc
              r * (b * derivative i (d ^ (k + 1))) =
                  (a * d) * (b * derivative i (d ^ (k + 1))) := by rw [ha]
              _ = b * d * (a * derivative i (d ^ (k + 1))) := by grind
              _ = b * d * (c * d ^ (k + 1)) := by rw [hc]
              _ = (b * c) * (d ^ (k + 1) * d) := by grind
              _ = (b * c) * d ^ (k + 1 + 1) :=
                congrArg (fun x => (b * c) * x)
                  (MvPoly.pow_succ d (k + 1)).symm
      rw [hg]
      apply dvd_gcdList
      intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hq
      · rcases List.mem_map.mp hp with ⟨i, _, rfl⟩
        exact hderivative i

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

def sqfProduct (factors : List (SqfFactor n R cmp)) :
    MvPoly n R cmp :=
  factors.foldl (fun acc factor =>
    acc * factor.factor ^ factor.multiplicity) 1

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
theorem sqfProduct_from (factors : List (SqfFactor n R cmp))
    (start : MvPoly n R cmp) :
    factors.foldl (fun acc factor =>
      acc * factor.factor ^ factor.multiplicity) start =
      start * sqfProduct factors := by
  induction factors generalizing start with
  | nil =>
      change start = start * 1
      exact (MvPoly.mul_one start).symm
  | cons factor factors ih =>
      simp only [List.foldl_cons]
      rw [ih]
      change (start * factor.factor ^ factor.multiplicity) *
          sqfProduct factors =
        start * (factors.foldl
          (fun acc factor => acc * factor.factor ^ factor.multiplicity)
          (1 * factor.factor ^ factor.multiplicity))
      rw [ih]
      grind

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
@[simp] theorem sqfProduct_nil :
    sqfProduct ([] : List (SqfFactor n R cmp)) = 1 := rfl

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
theorem sqfProduct_cons (factor : SqfFactor n R cmp)
    (factors : List (SqfFactor n R cmp)) :
    sqfProduct (factor :: factors) =
      factor.factor ^ factor.multiplicity * sqfProduct factors := by
  unfold sqfProduct
  rw [List.foldl_cons, sqfProduct_from]
  exact congrArg (fun x => x * sqfProduct factors)
    (MvPoly.one_mul _)

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
private theorem sqfProduct_merge (entry : SqfFactor n R cmp)
    (factors : List (SqfFactor n R cmp)) :
    sqfProduct (mergeSqfFactor entry factors) =
      entry.factor ^ entry.multiplicity * sqfProduct factors := by
  induction factors with
  | nil =>
      rw [mergeSqfFactor, sqfProduct_cons, sqfProduct_nil]
  | cons head tail ih =>
      simp only [mergeSqfFactor]
      split
      · rw [sqfProduct_cons, sqfProduct_cons]
      · split
        · rename_i heq
          have hpow : (entry.factor * head.factor) ^ entry.multiplicity =
              entry.factor ^ entry.multiplicity *
                head.factor ^ entry.multiplicity :=
            Lean.Grind.CommSemiring.mul_pow _ _ _
          rw [sqfProduct_cons, sqfProduct_cons]
          rw [hpow, heq]
          grind
        · rw [sqfProduct_cons, sqfProduct_cons, ih]
          grind

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
theorem sqfProduct_merge_fold
    (entries acc : List (SqfFactor n R cmp)) :
    sqfProduct (entries.foldl
      (fun acc entry => mergeSqfFactor entry acc) acc) =
      sqfProduct entries * sqfProduct acc := by
  induction entries generalizing acc with
  | nil =>
      rw [List.foldl_nil, sqfProduct_nil, MvPoly.one_mul]
  | cons entry entries ih =>
      rw [List.foldl_cons, ih, sqfProduct_merge]
      rw [sqfProduct_cons]
      grind

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
theorem sqfProduct_append
    (left right : List (SqfFactor n R cmp)) :
    sqfProduct (left ++ right) = sqfProduct left * sqfProduct right := by
  induction left with
  | nil => rw [List.nil_append, sqfProduct_nil, MvPoly.one_mul]
  | cons factor factors ih =>
      rw [List.cons_append, sqfProduct_cons, sqfProduct_cons, ih]
      grind

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
theorem constIn_C
    {m : Nat}
    {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    {lowerOrder : Mono m → Mono m → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    [Std.TransCmp lowerOrder] [Std.LawfulEqCmp lowerOrder]
    (i : Fin (m + 1)) (c : R) :
    constIn (cmp := order) i lowerOrder (C c) = C c := by
  apply MvPoly.ext
  intro monomial
  unfold constIn
  rw [← insertVar_removeVar i monomial, ofUnivariate_coeff,
    DensePoly.coeff_C, insertVar_removeVar]
  by_cases hdegree : Mono.degreeOf i monomial = 0
  · rw [ite_eq_left hdegree, coeff_C, coeff_C]
    have hzero : insertVar i 0 (Mono.zero : Mono m) = Mono.zero := by
      apply Vector.ext
      intro j hj
      simp [insertVar, Mono.zero]
    have hmonomial :
        monomial = Mono.zero ↔ removeVar i monomial = Mono.zero := by
      constructor
      · intro h
        subst monomial
        simp [removeVar, Mono.zero]
      · intro h
        calc
          monomial = insertVar i (Mono.degreeOf i monomial)
              (removeVar i monomial) := (insertVar_removeVar i monomial).symm
          _ = insertVar i 0 Mono.zero := by rw [hdegree, h]
          _ = Mono.zero := hzero
    simp only [hmonomial]
  · rw [ite_eq_right hdegree]
    have hmonomial : monomial ≠ Mono.zero := by
      intro h
      subst monomial
      exact hdegree (by
        unfold Mono.degreeOf
        exact Mono.getElem_zero i)
    change coeff (removeVar i monomial) (0 : MvPoly m R lowerOrder) =
      coeff monomial (C c : MvPoly (m + 1) R order)
    rw [coeff_zero, coeff_C, ite_eq_right hmonomial]

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
private theorem constIn_pow
    {m : Nat}
    {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    {lowerOrder : Mono m → Mono m → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    [Std.TransCmp lowerOrder] [Std.LawfulEqCmp lowerOrder]
    (i : Fin (m + 1)) (p : MvPoly m R lowerOrder) :
    ∀ k : Nat,
      constIn (cmp := order) i lowerOrder (p ^ k) =
        constIn i lowerOrder p ^ k := by
  intro k
  induction k with
  | zero => rw [MvPoly.pow_zero, MvPoly.pow_zero, constIn_one]
  | succ k ih =>
      rw [MvPoly.pow_succ, MvPoly.pow_succ, constIn_mul, ih]

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
theorem sqfProduct_map_constIn
    {m : Nat}
    {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    {lowerOrder : Mono m → Mono m → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    [Std.TransCmp lowerOrder] [Std.LawfulEqCmp lowerOrder]
    (i : Fin (m + 1)) (factors : List (SqfFactor m R lowerOrder)) :
    sqfProduct (factors.map fun factor =>
      { factor := constIn (cmp := order) i lowerOrder factor.factor
        multiplicity := factor.multiplicity }) =
      constIn i lowerOrder (sqfProduct factors) := by
  induction factors with
  | nil => rw [List.map_nil, sqfProduct_nil, sqfProduct_nil, constIn_one]
  | cons factor factors ih =>
      rw [List.map_cons, sqfProduct_cons, sqfProduct_cons, ih,
        ← constIn_pow, ← constIn_mul]

private theorem eq_constIn_of_dvd
    {m : Nat}
    {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    {lowerOrder : Mono m → Mono m → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    [Std.TransCmp lowerOrder] [Std.LawfulEqCmp lowerOrder]
    [IsMonomialOrder order] [IsMonomialOrder lowerOrder]
    (i : Fin (m + 1)) {d : MvPoly (m + 1) R order}
    {r : MvPoly m R lowerOrder} (hr : r ≠ 0)
    (hdiv : d ∣ constIn (cmp := order) i lowerOrder r) :
    ∃ c : MvPoly m R lowerOrder, d = constIn i lowerOrder c := by
  rcases hdiv with ⟨q, hproduct⟩
  let dv := toUnivariate i lowerOrder d
  let qv := toUnivariate i lowerOrder q
  have hview : qv * dv = DensePoly.C r := by
    calc
      qv * dv = toUnivariate i lowerOrder (q * d) :=
        (toUnivariate_mul i q d).symm
      _ = DensePoly.C r := by rw [← hproduct, toUnivariate_constIn]
  have hconstant0 : DensePoly.C r ≠
      (0 : DensePoly (MvPoly m R lowerOrder)) := by
    intro hzero
    have hsize := congrArg DensePoly.size hzero
    rw [DensePoly.size_C_of_ne_zero hr, DensePoly.size_zero] at hsize
    omega
  have hproduct0 : qv * dv ≠ 0 := by rw [hview]; exact hconstant0
  have hqv0 : qv ≠ 0 := by
    intro hzero
    apply hproduct0
    rw [hzero, DensePoly.zero_mul]
  have hdv0 : dv ≠ 0 := by
    intro hzero
    apply hproduct0
    rw [DensePoly.mul_comm_poly qv, hzero, DensePoly.zero_mul]
  have hqpos : 0 < qv.size := Nat.pos_of_ne_zero fun hzero =>
    hqv0 ((DensePoly.size_eq_zero_iff qv).mp hzero)
  have hdpos : 0 < dv.size := Nat.pos_of_ne_zero fun hzero =>
    hdv0 ((DensePoly.size_eq_zero_iff dv).mp hzero)
  have htop : qv.leadingCoeff * dv.leadingCoeff ≠ 0 := by
    intro hzero
    rcases GcdDomainLaws.no_zero_div qv.leadingCoeff dv.leadingCoeff hzero with
      hq | hd
    · exact DensePoly.leadingCoeff_ne_zero_of_pos_size qv hqpos hq
    · exact DensePoly.leadingCoeff_ne_zero_of_pos_size dv hdpos hd
  have hsize := DensePoly.size_mul_of_top_ne qv dv hqpos hdpos htop
  have hdle : dv.size ≤ 1 := by
    rw [hview, DensePoly.size_C_of_ne_zero hr] at hsize
    omega
  let c := dv.coeff 0
  have hdense : dv = DensePoly.C c := by
    apply DensePoly.ext_coeff
    intro k
    rw [DensePoly.coeff_C]
    by_cases hk : k = 0
    · rw [ite_eq_left hk, hk]
    · rw [ite_eq_right hk]
      exact DensePoly.coeff_eq_zero_of_size_le dv (by omega)
  refine ⟨c, ?_⟩
  calc
    d = ofUnivariate (cmp := order) i lowerOrder dv :=
      (ofUnivariate_toUnivariate i d).symm
    _ = ofUnivariate (cmp := order) i lowerOrder (DensePoly.C c) := by
      rw [hdense]
    _ = constIn i lowerOrder c := rfl

private theorem coeff_dvd_of_constIn_dvd
    {m : Nat}
    {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    {lowerOrder : Mono m → Mono m → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    [Std.TransCmp lowerOrder] [Std.LawfulEqCmp lowerOrder]
    [IsMonomialOrder order] [IsMonomialOrder lowerOrder]
    (i : Fin (m + 1)) {c : MvPoly m R lowerOrder}
    {d f : MvPoly (m + 1) R order}
    (hd : d = constIn i lowerOrder c) (hdf : d ∣ f) (k : Nat) :
    c ∣ (toUnivariate i lowerOrder f).coeff k := by
  rcases hdf with ⟨q, hq⟩
  refine ⟨(toUnivariate i lowerOrder q).coeff k, ?_⟩
  calc
    (toUnivariate i lowerOrder f).coeff k =
        (toUnivariate i lowerOrder (q * d)).coeff k := by rw [hq]
    _ = (toUnivariate i lowerOrder (constIn i lowerOrder c * q)).coeff k := by
      rw [hd, MvPoly.mul_comm q]
    _ = c * (toUnivariate i lowerOrder q).coeff k :=
      coeff_constIn_mul i c q k
    _ = (toUnivariate i lowerOrder q).coeff k * c := MvPoly.mul_comm _ _

private theorem common_coefficient {p : MvPoly n R cmp} {d : R}
    (hd : ∀ c, c ∈ coefficientList p → d ∣ c) :
    ∀ m, d ∣ coeff m p := by
  intro m
  by_cases hm : m ∈ p.monomials
  · rcases List.mem_map.mp hm with ⟨term, hterm, hmono⟩
    rcases term with ⟨termMono, termCoeff⟩
    simp only at hmono
    subst termMono
    rw [coeff_eq_of_mem_terms p hterm]
    apply hd termCoeff
    exact List.mem_map.mpr ⟨(m, termCoeff), hterm, rfl⟩
  · rw [coeff_eq_zero_of_not_mem m p hm]
    apply (LawfulGcdOps.dvd_iff d 0).mpr
    exact ⟨0, (Lean.Grind.Semiring.mul_zero d).symm⟩

theorem primitive_constIn
    {m : Nat}
    {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    {lowerOrder : Mono m → Mono m → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    [Std.TransCmp lowerOrder] [Std.LawfulEqCmp lowerOrder]
    [IsMonomialOrder order] [IsMonomialOrder lowerOrder]
    (i : Fin (m + 1)) {p : MvPoly m R lowerOrder}
    (hp : Primitive p) : Primitive (constIn (cmp := order) i lowerOrder p) := by
  intro d hd
  apply hp d
  intro c hc
  rcases List.mem_map.mp hc with ⟨term, hterm, rfl⟩
  rcases term with ⟨monomial, coefficient⟩
  have hcommon := common_coefficient hd (insertVar i 0 monomial)
  have hcoefficient := coeff_eq_of_mem_terms p hterm
  have hembedCoeff :
      coeff monomial p = coeff (insertVar i 0 monomial)
        (constIn (cmp := order) i lowerOrder p) := by
    calc
      coeff monomial p =
          coeff monomial
            ((toUnivariate i lowerOrder
              (constIn (cmp := order) i lowerOrder p)).coeff 0) := by
        rw [toUnivariate_constIn, DensePoly.coeff_C, ite_eq_left rfl]
      _ = coeff (insertVar i 0 monomial)
            (constIn (cmp := order) i lowerOrder p) :=
        toUnivariate_coeff i _ 0 monomial
  rw [← hcoefficient]
  rw [hembedCoeff]
  exact hcommon

omit [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
theorem isConst_of_constIn
    {m : Nat}
    {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    {lowerOrder : Mono m → Mono m → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    [Std.TransCmp lowerOrder] [Std.LawfulEqCmp lowerOrder]
    (i : Fin (m + 1)) {p : MvPoly m R lowerOrder}
    (hp : IsConst (constIn (cmp := order) i lowerOrder p)) : IsConst p := by
  let c := coeff Mono.zero (constIn (cmp := order) i lowerOrder p)
  have heq : constIn (cmp := order) i lowerOrder p = C c :=
    eq_C_of_vars_eq_nil _ hp
  have heq' : constIn (cmp := order) i lowerOrder p =
      constIn i lowerOrder (C c) := by rw [constIn_C]; exact heq
  have hpC : p = C c := constIn_injective i heq'
  rw [hpC]
  exact isConst_C c

omit [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
private theorem isConst_constIn
    {m : Nat}
    {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    {lowerOrder : Mono m → Mono m → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    [Std.TransCmp lowerOrder] [Std.LawfulEqCmp lowerOrder]
    (i : Fin (m + 1)) {p : MvPoly m R lowerOrder} (hp : IsConst p) :
    IsConst (constIn (cmp := order) i lowerOrder p) := by
  let c := coeff Mono.zero p
  have hpC : p = C c := eq_C_of_vars_eq_nil p hp
  rw [hpC, constIn_C]
  exact isConst_C c

theorem squarefree_constIn
    {m : Nat}
    {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    {lowerOrder : Mono m → Mono m → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    [Std.TransCmp lowerOrder] [Std.LawfulEqCmp lowerOrder]
    [IsMonomialOrder order] [IsMonomialOrder lowerOrder]
    (i : Fin (m + 1)) {p : MvPoly m R lowerOrder}
    (hp : Squarefree p) :
    Squarefree (constIn (cmp := order) i lowerOrder p) := by
  refine ⟨fun hzero => hp.1 (constIn_injective i (hzero.trans (constIn_zero i).symm)), ?_⟩
  intro d hsquare
  have hp0 := hp.1
  have hdDvd : d ∣ constIn (cmp := order) i lowerOrder p := by
    rcases hsquare with ⟨q, hq⟩
    refine ⟨q * d, ?_⟩
    calc
      constIn (cmp := order) i lowerOrder p = q * (d * d) := hq
      _ = (q * d) * d := by grind
  rcases eq_constIn_of_dvd i hp0 hdDvd with ⟨c, hd⟩
  have hcSquare : c * c ∣ p := by
    have hconstSquare : d * d =
        constIn (cmp := order) i lowerOrder (c * c) := by
      rw [hd, constIn_mul]
    have hdiv : constIn (cmp := order) i lowerOrder (c * c) ∣
        constIn i lowerOrder p := by rw [← hconstSquare]; exact hsquare
    have hcoeff := coeff_dvd_of_constIn_dvd i rfl hdiv 0
    simpa using hcoeff
  rw [hd]
  exact isConst_constIn i (hp.2 c hcSquare)

theorem coprime_constIn_of_content_one
    {m : Nat}
    {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    {lowerOrder : Mono m → Mono m → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    [Std.TransCmp lowerOrder] [Std.LawfulEqCmp lowerOrder]
    [IsMonomialOrder order] [IsMonomialOrder lowerOrder]
    (i : Fin (m + 1)) {a : MvPoly m R lowerOrder}
    {b : MvPoly (m + 1) R order} (ha0 : a ≠ 0)
    (hbContent : contentIn i lowerOrder b = 1) :
    ∀ d, d ∣ constIn (cmp := order) i lowerOrder a → d ∣ b →
      polyIsUnit d = true := by
  intro d hdA hdB
  rcases eq_constIn_of_dvd i ha0 hdA with ⟨c, hd⟩
  have hcContent : c ∣ contentIn i lowerOrder b := by
    apply dvd_contentIn i lowerOrder b c
    intro k
    exact coeff_dvd_of_constIn_dvd i hd hdB k
  rw [hbContent] at hcContent
  rcases hcContent with ⟨v, hv⟩
  apply (polyIsUnit_iff d).mpr
  refine ⟨constIn (cmp := order) i lowerOrder v, ?_⟩
  rw [hd, ← constIn_mul]
  have hcv : c * v = 1 := by
    calc
      c * v = v * c := MvPoly.mul_comm ..
      _ = 1 := hv.symm
  rw [hcv, constIn_one]

theorem coprime_constIn
    {m : Nat}
    {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    {lowerOrder : Mono m → Mono m → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    [Std.TransCmp lowerOrder] [Std.LawfulEqCmp lowerOrder]
    [IsMonomialOrder order] [IsMonomialOrder lowerOrder]
    (i : Fin (m + 1)) {a b : MvPoly m R lowerOrder} (ha0 : a ≠ 0)
    (hab : ∀ d, d ∣ a → d ∣ b → polyIsUnit d = true) :
    ∀ d, d ∣ constIn (cmp := order) i lowerOrder a →
      d ∣ constIn (cmp := order) i lowerOrder b → polyIsUnit d = true := by
  intro d hdA hdB
  rcases eq_constIn_of_dvd i ha0 hdA with ⟨c, hd⟩
  have hcA : c ∣ a := by
    have hcoeff := coeff_dvd_of_constIn_dvd i rfl (hd ▸ hdA) 0
    simpa using hcoeff
  have hcB : c ∣ b := by
    have hcoeff := coeff_dvd_of_constIn_dvd i rfl (hd ▸ hdB) 0
    simpa using hcoeff
  rcases (polyIsUnit_iff c).mp (hab c hcA hcB) with ⟨v, hv⟩
  apply (polyIsUnit_iff d).mpr
  refine ⟨constIn (cmp := order) i lowerOrder v, ?_⟩
  rw [hd, ← constIn_mul]
  rw [hv, constIn_one]

private theorem squarefree_mul_of_coprime [IsMonomialOrder cmp]
    {p q : MvPoly n R cmp} (hp : Squarefree p) (hq : Squarefree q)
    (hcoprime : ∀ d, d ∣ p → d ∣ q → polyIsUnit d = true) :
    Squarefree (p * q) := by
  have hpq0 : p * q ≠ 0 := by
    intro hzero
    rcases GcdDomainLaws.no_zero_div p q hzero with hp0 | hq0
    · exact hp.1 hp0
    · exact hq.1 hq0
  refine ⟨hpq0, ?_⟩
  intro r hrr
  have hr0 : r ≠ 0 := by
    intro hr
    subst r
    rcases hrr with ⟨a, ha⟩
    rw [MvPoly.zero_mul, MvPoly.mul_zero] at ha
    exact hpq0 ha
  let a := gcd r p
  let b := quotient r a
  let p₁ := quotient p a
  rcases gcd_quotients (b := r) (d := p) hr0 with
    ⟨ha0, hba, hp₁a, hcopBP⟩
  change a ≠ 0 at ha0
  change b * a = r at hba
  change p₁ * a = p at hp₁a
  have hb0 : b ≠ 0 := by
    intro hb
    apply hr0
    rw [← hba, hb, MvPoly.zero_mul]
  have haP : a ∣ p := gcd_dvd_right r p
  have hcopQA : ∀ e, e ∣ q → e ∣ a → ∃ u, e * u = 1 := by
    intro e heQ heA
    exact (polyIsUnit_iff e).mp
      (hcoprime e (Hex.dvdTrans heA haP) heQ)
  rcases hrr with ⟨x, hx⟩
  have hp₁q : p₁ * q = (x * b * b) * a := by
    have hzero : a * (p₁ * q - (x * b * b) * a) = 0 := by
      calc
        a * (p₁ * q - (x * b * b) * a) =
            (p₁ * a) * q - x * ((b * a) * (b * a)) := by grind
        _ = p * q - x * (r * r) := by rw [hp₁a, hba]
        _ = 0 := by rw [hx]; grind
    rcases GcdDomainLaws.no_zero_div a _ hzero with hzero | hcancel
    · exact False.elim (ha0 hzero)
    · grind
  have haP₁Q : a ∣ p₁ * q := ⟨x * b * b, hp₁q⟩
  have haP₁A : a ∣ p₁ * a := ⟨p₁, rfl⟩
  have haP₁ : a ∣ p₁ :=
    CoprimeCancelLaws.cancel_coprime p₁ q a a hcopQA haP₁Q haP₁A
  have haSquareP : a * a ∣ p := by
    rcases haP₁ with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    calc
      p = p₁ * a := hp₁a.symm
      _ = (t * a) * a := by rw [ht]
      _ = t * (a * a) := by grind
  have haConst : IsConst a := hp.2 a haSquareP
  have hbSquareP₁Q : b * b ∣ p₁ * q := by
    refine ⟨x * a, ?_⟩
    calc
      p₁ * q = (x * b * b) * a := hp₁q
      _ = (x * a) * (b * b) := by grind
  have hbP₁Q : b ∣ p₁ * q := by
    exact Hex.dvdTrans
      (show b ∣ b * b from ⟨b, rfl⟩) hbSquareP₁Q
  have hbQB : b ∣ q * b := ⟨q, rfl⟩
  have hcopP₁B : ∀ e, e ∣ p₁ → e ∣ b → ∃ u, e * u = 1 := by
    intro e heP₁ heB
    exact (polyIsUnit_iff e).mp (hcopBP e heB heP₁)
  have hbQ : b ∣ q :=
    CoprimeCancelLaws.cancel_coprime q p₁ b b hcopP₁B
      (by rw [MvPoly.mul_comm]; exact hbP₁Q) hbQB
  rcases hbQ with ⟨q₁, hq₁⟩
  rcases hbSquareP₁Q with ⟨y, hy⟩
  have hbP₁Q₁ : b ∣ p₁ * q₁ := by
    have hzero : b * (p₁ * q₁ - y * b) = 0 := by
      calc
        b * (p₁ * q₁ - y * b) = p₁ * (q₁ * b) - y * (b * b) := by
          grind
        _ = p₁ * q - y * (b * b) := by rw [hq₁]
        _ = 0 := by rw [hy]; grind
    rcases GcdDomainLaws.no_zero_div b _ hzero with hzero | hcancel
    · exact False.elim (hb0 hzero)
    · refine ⟨y, ?_⟩
      grind
  have hbQ₁B : b ∣ q₁ * b := ⟨q₁, rfl⟩
  have hbQ₁ : b ∣ q₁ :=
    CoprimeCancelLaws.cancel_coprime q₁ p₁ b b hcopP₁B
      (by rw [MvPoly.mul_comm]; exact hbP₁Q₁) hbQ₁B
  have hbSquareQ : b * b ∣ q := by
    rcases hbQ₁ with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    calc
      q = q₁ * b := hq₁
      _ = (z * b) * b := by rw [hz]
      _ = z * (b * b) := by grind
  have hbConst : IsConst b := hq.2 b hbSquareQ
  let ca := coeff Mono.zero a
  let cb := coeff Mono.zero b
  have haC : a = C ca := eq_C_of_vars_eq_nil a haConst
  have hbC : b = C cb := eq_C_of_vars_eq_nil b hbConst
  have hrC : r = C (cb * ca) := by
    calc
      r = b * a := hba.symm
      _ = C cb * C ca := by rw [hbC, haC]
      _ = C (cb * ca) := C_mul_C cb ca
  rw [hrC]
  exact isConst_C _

private theorem coprime_mul_left [IsMonomialOrder cmp]
    {p q r : MvPoly n R cmp} (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hpr : ∀ d, d ∣ p → d ∣ r → polyIsUnit d = true)
    (hqr : ∀ d, d ∣ q → d ∣ r → polyIsUnit d = true) :
    ∀ d, d ∣ p * q → d ∣ r → polyIsUnit d = true := by
  intro d hdPQ hdR
  have hpq0 : p * q ≠ 0 := by
    intro hzero
    rcases GcdDomainLaws.no_zero_div p q hzero with hzero | hzero
    · exact hp0 hzero
    · exact hq0 hzero
  have hd0 : d ≠ 0 := by
    intro hzero
    subst d
    rcases hdPQ with ⟨a, ha⟩
    rw [MvPoly.mul_zero] at ha
    exact hpq0 ha
  let a := gcd d p
  let b := quotient d a
  let p₁ := quotient p a
  rcases gcd_quotients (b := d) (d := p) hd0 with
    ⟨ha0, hba, hp₁a, hcopBP⟩
  change a ≠ 0 at ha0
  change b * a = d at hba
  change p₁ * a = p at hp₁a
  have hb0 : b ≠ 0 := by
    intro hzero
    apply hd0
    rw [← hba, hzero, MvPoly.zero_mul]
  have haP : a ∣ p := gcd_dvd_right d p
  have haD : a ∣ d := gcd_dvd_left d p
  have haR : a ∣ r := Hex.dvdTrans haD hdR
  have haUnit : polyIsUnit a = true := hpr a haP haR
  rcases hdPQ with ⟨x, hx⟩
  have hbP₁Q : b ∣ p₁ * q := by
    have hzero : a * (p₁ * q - x * b) = 0 := by
      calc
        a * (p₁ * q - x * b) = (p₁ * a) * q - x * (b * a) := by
          grind
        _ = p * q - x * d := by rw [hp₁a, hba]
        _ = 0 := by rw [hx]; grind
    rcases GcdDomainLaws.no_zero_div a _ hzero with hzero | hcancel
    · exact False.elim (ha0 hzero)
    · refine ⟨x, ?_⟩
      grind
  have hcopP₁B : ∀ e, e ∣ p₁ → e ∣ b → ∃ u, e * u = 1 := by
    intro e heP₁ heB
    exact (polyIsUnit_iff e).mp (hcopBP e heB heP₁)
  have hbQB : b ∣ q * b := ⟨q, rfl⟩
  have hbQ : b ∣ q :=
    CoprimeCancelLaws.cancel_coprime q p₁ b b hcopP₁B
      (by rw [MvPoly.mul_comm]; exact hbP₁Q) hbQB
  have hbD : b ∣ d := by
    refine ⟨a, ?_⟩
    rw [MvPoly.mul_comm]
    exact hba.symm
  have hbR : b ∣ r := Hex.dvdTrans hbD hdR
  have hbUnit : polyIsUnit b = true := hqr b hbQ hbR
  rcases (polyIsUnit_iff a).mp haUnit with ⟨ia, hia⟩
  rcases (polyIsUnit_iff b).mp hbUnit with ⟨ib, hib⟩
  apply (polyIsUnit_iff d).mpr
  refine ⟨ia * ib, ?_⟩
  calc
    d * (ia * ib) = (b * ib) * (a * ia) := by rw [← hba]; grind
    _ = 1 := by rw [hib, hia, MvPoly.one_mul]

private theorem nonconstant_mul_left [NatNoZero R]
    {m : Nat} {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    {p q : MvPoly (m + 1) R order} (hp : ¬ IsConst p) (hq0 : q ≠ 0) :
    ¬ IsConst (p * q) := by
  intro hpq
  cases hvars : p.vars with
  | nil => exact hp hvars
  | cons i tail =>
      have hi : i ∈ p.vars := by rw [hvars]; simp
      let pv := toUnivariate i Mono.lex p
      let qv := toUnivariate i Mono.lex q
      have hpvSize : 1 < pv.size := view_size_gt_one_of_mem_vars i p hi
      have hqv0 : qv ≠ 0 := by
        intro hzero
        apply hq0
        calc
          q = ofUnivariate i Mono.lex qv :=
            (ofUnivariate_toUnivariate i q).symm
          _ = 0 := by rw [hzero]; rfl
      have hqvPos : 0 < qv.size :=
        Nat.pos_of_ne_zero
          (fun h => hqv0 ((DensePoly.size_eq_zero_iff qv).mp h))
      have hpvPos : 0 < pv.size := by omega
      have htop : pv.leadingCoeff * qv.leadingCoeff ≠
          (0 : MvPoly m R Mono.lex) := by
        intro hzero
        rcases GcdDomainLaws.no_zero_div _ _ hzero with hl | hr
        · exact (DensePoly.leadingCoeff_ne_zero_of_pos_size pv hpvPos) hl
        · exact (DensePoly.leadingCoeff_ne_zero_of_pos_size qv hqvPos) hr
      have hsize := DensePoly.size_mul_of_top_ne pv qv hpvPos hqvPos htop
      have hpqC : p * q = C (coeff Mono.zero (p * q)) :=
        eq_C_of_vars_eq_nil (p * q) hpq
      have hsizeC := congrArg
        (fun f => (toUnivariate i Mono.lex f).size) hpqC
      rw [toUnivariate_mul, hsize] at hsizeC
      have hCle :
          (toUnivariate i Mono.lex
            (C (coeff Mono.zero (p * q)) : MvPoly (m + 1) R order)).size ≤ 1 := by
        rw [← constIn_C (order := order) (lowerOrder := Mono.lex) i,
          toUnivariate_constIn]
        exact DensePoly.size_C_le_one _
      omega

private theorem nonconstant_mul [NatNoZero R]
    {p q : MvPoly n R cmp} (hp : ¬ IsConst p) (hq0 : q ≠ 0) :
    ¬ IsConst (p * q) := by
  cases n with
  | zero =>
      exfalso
      apply hp
      unfold IsConst
      rw [vars_eq]
      simp [Mono.support]
  | succ m => exact nonconstant_mul_left hp hq0

def CoprimePoly (p q : MvPoly n R cmp) : Prop :=
  ∀ d, d ∣ p → d ∣ q → polyIsUnit d = true

private theorem coprimePoly_symm {p q : MvPoly n R cmp}
    (hpq : CoprimePoly p q) : CoprimePoly q p := by
  intro d hdq hdp
  exact hpq d hdp hdq

private theorem coprimePoly_mul_left [IsMonomialOrder cmp]
    {p q r : MvPoly n R cmp} (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hpr : CoprimePoly p r) (hqr : CoprimePoly q r) :
    CoprimePoly (p * q) r :=
  coprime_mul_left hp0 hq0 hpr hqr

structure FactorProperties
    (factors : List (SqfFactor n R cmp)) : Prop where
  squarefree : ∀ factor ∈ factors, Squarefree factor.factor
  primitive : ∀ factor ∈ factors, Primitive factor.factor
  nonconstant : ∀ factor ∈ factors, ¬ IsConst factor.factor
  pairwise : factors.Pairwise fun left right =>
    CoprimePoly left.factor right.factor

theorem properties_nil :
    FactorProperties ([] : List (SqfFactor n R cmp)) :=
  { squarefree := by simp
    primitive := by simp
    nonconstant := by simp
    pairwise := by simp }

theorem coprime_of_mem
    {factors : List (SqfFactor n R cmp)}
    (hpairwise : factors.Pairwise fun left right =>
      CoprimePoly left.factor right.factor) :
    ∀ left ∈ factors, ∀ right ∈ factors, left ≠ right →
      CoprimePoly left.factor right.factor := by
  induction factors with
  | nil => simp
  | cons head tail ih =>
      have hsource := List.pairwise_cons.mp hpairwise
      intro left hleft right hright hne
      rcases List.mem_cons.mp hleft with hleftEq | hleft
      · subst left
        rcases List.mem_cons.mp hright with hrightEq | hright
        · subst right
          exact False.elim (hne rfl)
        · exact hsource.1 right hright
      · rcases List.mem_cons.mp hright with hrightEq | hright
        · subst right
          exact coprimePoly_symm (hsource.1 left hleft)
        · exact ih hsource.2 left hleft right hright hne

def CrossFactors (left right : List (SqfFactor n R cmp)) : Prop :=
  ∀ a ∈ left, ∀ b ∈ right, CoprimePoly a.factor b.factor

private theorem coprime_merge [IsMonomialOrder cmp]
    (entry : SqfFactor n R cmp)
    {factors : List (SqfFactor n R cmp)} {p : MvPoly n R cmp}
    (hentry0 : entry.factor ≠ 0)
    (hfactors0 : ∀ factor ∈ factors, factor.factor ≠ 0)
    (hentry : CoprimePoly p entry.factor)
    (hfactors : ∀ factor ∈ factors, CoprimePoly p factor.factor) :
    ∀ factor ∈ mergeSqfFactor entry factors,
      CoprimePoly p factor.factor := by
  induction factors with
  | nil =>
      intro factor hfactor
      simp only [mergeSqfFactor, List.mem_cons, List.not_mem_nil,
        or_false] at hfactor
      subst factor
      exact hentry
  | cons head tail ih =>
      have hhead0 := hfactors0 head (by simp)
      have htail0 : ∀ factor ∈ tail, factor.factor ≠ 0 := by
        intro factor hfactor
        exact hfactors0 factor (by simp [hfactor])
      have hhead := hfactors head (by simp)
      have htail : ∀ factor ∈ tail, CoprimePoly p factor.factor := by
        intro factor hfactor
        exact hfactors factor (by simp [hfactor])
      simp only [mergeSqfFactor]
      split
      · intro factor hfactor
        simp only [List.mem_cons] at hfactor
        rcases hfactor with rfl | hfactor
        · exact hentry
        · exact hfactors factor (by simp [hfactor])
      · split
        · intro factor hfactor
          simp only [List.mem_cons] at hfactor
          rcases hfactor with rfl | hfactor
          · apply coprimePoly_symm
            apply coprimePoly_mul_left hentry0 hhead0
            · exact coprimePoly_symm hentry
            · exact coprimePoly_symm hhead
          · exact htail factor hfactor
        · intro factor hfactor
          simp only [List.mem_cons] at hfactor
          rcases hfactor with rfl | hfactor
          · exact hhead
          · exact ih htail0 htail factor hfactor

private theorem properties_merge [NatNoZero R] [IsMonomialOrder cmp]
    (entry : SqfFactor n R cmp) {factors : List (SqfFactor n R cmp)}
    (hentrySqf : Squarefree entry.factor)
    (hentryPrimitive : Primitive entry.factor)
    (hentryNonconst : ¬ IsConst entry.factor)
    (hfactors : FactorProperties factors)
    (hcross : ∀ factor ∈ factors,
      CoprimePoly entry.factor factor.factor) :
    FactorProperties (mergeSqfFactor entry factors) := by
  induction factors with
  | nil =>
      simp only [mergeSqfFactor]
      exact
        { squarefree := by simpa
          primitive := by simpa
          nonconstant := by simpa
          pairwise := by simp }
  | cons head tail ih =>
      have hheadSqf := hfactors.squarefree head (by simp)
      have hheadPrimitive := hfactors.primitive head (by simp)
      have hheadNonconst := hfactors.nonconstant head (by simp)
      have htail : FactorProperties tail :=
        { squarefree := by
            intro factor hfactor
            exact hfactors.squarefree factor (by simp [hfactor])
          primitive := by
            intro factor hfactor
            exact hfactors.primitive factor (by simp [hfactor])
          nonconstant := by
            intro factor hfactor
            exact hfactors.nonconstant factor (by simp [hfactor])
          pairwise := (List.pairwise_cons.mp hfactors.pairwise).2 }
      have hheadTail : ∀ factor ∈ tail,
          CoprimePoly head.factor factor.factor :=
        (List.pairwise_cons.mp hfactors.pairwise).1
      have hentryHead := hcross head (by simp)
      have hentryTail : ∀ factor ∈ tail,
          CoprimePoly entry.factor factor.factor := by
        intro factor hfactor
        exact hcross factor (by simp [hfactor])
      simp only [mergeSqfFactor]
      split
      · exact
          { squarefree := by
              intro factor hfactor
              simp only [List.mem_cons] at hfactor
              rcases hfactor with rfl | hfactor
              · exact hentrySqf
              · exact hfactors.squarefree factor
                  (by simpa only [List.mem_cons] using hfactor)
            primitive := by
              intro factor hfactor
              simp only [List.mem_cons] at hfactor
              rcases hfactor with rfl | hfactor
              · exact hentryPrimitive
              · exact hfactors.primitive factor
                  (by simpa only [List.mem_cons] using hfactor)
            nonconstant := by
              intro factor hfactor
              simp only [List.mem_cons] at hfactor
              rcases hfactor with rfl | hfactor
              · exact hentryNonconst
              · exact hfactors.nonconstant factor
                  (by simpa only [List.mem_cons] using hfactor)
            pairwise := List.Pairwise.cons hcross hfactors.pairwise }
      · split
        · exact
            { squarefree := by
                intro factor hfactor
                simp only [List.mem_cons] at hfactor
                rcases hfactor with rfl | hfactor
                · exact squarefree_mul_of_coprime hentrySqf hheadSqf hentryHead
                · exact htail.squarefree factor hfactor
              primitive := by
                intro factor hfactor
                simp only [List.mem_cons] at hfactor
                rcases hfactor with rfl | hfactor
                · exact primitive_mul hentryPrimitive hheadPrimitive
                · exact htail.primitive factor hfactor
              nonconstant := by
                intro factor hfactor
                simp only [List.mem_cons] at hfactor
                rcases hfactor with rfl | hfactor
                · exact nonconstant_mul hentryNonconst hheadSqf.1
                · exact htail.nonconstant factor hfactor
              pairwise := by
                apply List.Pairwise.cons
                · intro factor hfactor
                  exact coprimePoly_mul_left hentrySqf.1 hheadSqf.1
                    (hentryTail factor hfactor) (hheadTail factor hfactor)
                · exact htail.pairwise }
        · have hmerged := ih htail hentryTail
          exact
            { squarefree := by
                intro factor hfactor
                simp only [List.mem_cons] at hfactor
                rcases hfactor with rfl | hfactor
                · exact hheadSqf
                · exact hmerged.squarefree factor hfactor
              primitive := by
                intro factor hfactor
                simp only [List.mem_cons] at hfactor
                rcases hfactor with rfl | hfactor
                · exact hheadPrimitive
                · exact hmerged.primitive factor hfactor
              nonconstant := by
                intro factor hfactor
                simp only [List.mem_cons] at hfactor
                rcases hfactor with rfl | hfactor
                · exact hheadNonconst
                · exact hmerged.nonconstant factor hfactor
              pairwise := by
                apply List.Pairwise.cons
                · apply coprime_merge entry hentrySqf.1
                  · intro factor hfactor
                    exact (htail.squarefree factor hfactor).1
                  · exact coprimePoly_symm hentryHead
                  · exact hheadTail
                · exact hmerged.pairwise }

theorem properties_merge_fold [NatNoZero R]
    [IsMonomialOrder cmp]
    (entries acc : List (SqfFactor n R cmp))
    (hentries : FactorProperties entries)
    (hacc : FactorProperties acc)
    (hcross : CrossFactors entries acc) :
    FactorProperties (entries.foldl
      (fun acc entry => mergeSqfFactor entry acc) acc) := by
  induction entries generalizing acc with
  | nil => simpa using hacc
  | cons entry entries ih =>
      have hentrySqf := hentries.squarefree entry (by simp)
      have hentryPrimitive := hentries.primitive entry (by simp)
      have hentryNonconst := hentries.nonconstant entry (by simp)
      have htail : FactorProperties entries :=
        { squarefree := by
            intro factor hfactor
            exact hentries.squarefree factor (by simp [hfactor])
          primitive := by
            intro factor hfactor
            exact hentries.primitive factor (by simp [hfactor])
          nonconstant := by
            intro factor hfactor
            exact hentries.nonconstant factor (by simp [hfactor])
          pairwise := (List.pairwise_cons.mp hentries.pairwise).2 }
      have hentryTail : ∀ factor ∈ entries,
          CoprimePoly entry.factor factor.factor :=
        (List.pairwise_cons.mp hentries.pairwise).1
      have hentryAcc : ∀ factor ∈ acc,
          CoprimePoly entry.factor factor.factor := by
        intro factor hfactor
        exact hcross entry (by simp) factor hfactor
      have hmerged := properties_merge entry hentrySqf hentryPrimitive
        hentryNonconst hacc hentryAcc
      apply ih (mergeSqfFactor entry acc) htail hmerged
      intro left hleft right hright
      exact coprime_merge entry hentrySqf.1
        (fun factor hfactor => (hacc.squarefree factor hfactor).1)
        (coprimePoly_symm (hentryTail left hleft))
        (fun factor hfactor => hcross left (by simp [hleft]) factor hfactor)
        right hright

def PositiveMultiplicities (factors : List (SqfFactor n R cmp)) : Prop :=
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
theorem positive_merge_fold (entries acc : List (SqfFactor n R cmp))
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

def SortedMultiplicities (factors : List (SqfFactor n R cmp)) : Prop :=
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
theorem sorted_merge_fold (entries acc : List (SqfFactor n R cmp))
    (hacc : SortedMultiplicities acc) :
    SortedMultiplicities (entries.foldl
      (fun acc entry => mergeSqfFactor entry acc) acc) := by
  induction entries generalizing acc with
  | nil => simpa
  | cons entry entries ih =>
      simp only [List.foldl_cons]
      exact ih _ (sorted_merge entry hacc)


end Hex.MvPoly
