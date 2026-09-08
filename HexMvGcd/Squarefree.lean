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
private theorem derivative_eq_zero_of_dvd (i : Fin n)
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
private theorem C_mul_C (a b : R) :
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
private theorem squarefree_primPart (p : MvPoly n R cmp) :
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
private theorem isConst_of_unit [IsMonomialOrder cmp]
    (d : MvPoly n R cmp)
    (hd : polyIsUnit d = true) : IsConst d := by
  rcases (polyIsUnit_iff d).mp hd with ⟨u, hu⟩
  rcases unit_eq_C LawfulGcdOps.one_ne_zero LawfulGcdOps.no_zero_div hu with
    ⟨c, _, hc, _⟩
  rw [hc]
  exact isConst_C c

omit [LawfulBezoutOps R] [GcdProducer R] in
private theorem unit_of_const_dvd_primitive [IsMonomialOrder cmp]
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
private theorem derivative_dvd_of_square_dvd (i : Fin n)
    {d q : MvPoly n R cmp} (h : d * d ∣ q) : d ∣ derivative i q := by
  rcases h with ⟨a, ha⟩
  refine ⟨derivative i a * d + a * (derivative i d + derivative i d), ?_⟩
  rw [ha, derivative_mul, derivative_mul]
  grind

@[simp] private theorem gcdList_derivatives_zero [IsMonomialOrder cmp] :
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

private def sqfBinomTerm {S : Type u} [Lean.Grind.CommRing S]
    (a b : S) (degree k : Nat) : S :=
  (Hex.Nat.choose degree k : S) *
    (sqfPow a (degree - k) * sqfPow b k)

private def sqfBinomSum {S : Type u} [Lean.Grind.CommRing S]
    (a b : S) (degree : Nat) : Nat → S
  | 0 => 0
  | k + 1 => sqfBinomSum a b degree k + sqfBinomTerm a b degree k

/-- In characteristic zero, the all-partials gcd criterion is equivalent to
relative squarefreeness for a primitive polynomial. -/
private theorem gcdList_unit_iff_squarefree_charZero [IsMonomialOrder cmp]
    [NatNoZero R]
    (q : MvPoly n R cmp) (hprimitive : Primitive q) :
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
      (isConst_of_derivatives_zero g hgDeriv)
      (gcdList_dvd (by simp))

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
def yunLoop [NatNoZero R] [IsMonomialOrder cmp] (i : Fin n) (fuel k : Nat)
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
private theorem positive_yunLoop [NatNoZero R] [IsMonomialOrder cmp]
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
private theorem sorted_yunLoop [NatNoZero R] [IsMonomialOrder cmp]
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

omit [LawfulBezoutOps R] [GcdProducer R] in
/-- The scalar and normalized primitive part reconstruct the input exactly. -/
theorem sqfPrimitiveSplit_product [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) :
    C (sqfPrimitiveSplit p).1 * (sqfPrimitiveSplit p).2 = p := by
  let scalar := content p
  let primitive := primPart p
  let unit := GcdOps.normUnit primitive.leadingCoeff
  let unitInv := GcdOps.exactDiv 1 unit
  change C (scalar * unitInv) * polyNormalize primitive = p
  by_cases hprimitive : primitive = 0
  · have hreconstruct := content_mul_primPart p
    change C scalar * primitive = p at hreconstruct
    rw [hprimitive, MvPoly.mul_zero] at hreconstruct
    rw [hprimitive, polyNormalize_zero, MvPoly.mul_zero]
    exact hreconstruct
  · cases hlead : primitive.leadingTerm with
    | none =>
        exact False.elim
          (hprimitive ((leadingTerm_eq_none_iff primitive).mp hlead))
    | some term =>
        rcases term with ⟨m, c⟩
        have hleadCoeff : primitive.leadingCoeff = c := by
          rw [leadingCoeff_eq, hlead]
          rfl
        have hunit : unit = GcdOps.normUnit c := by
          simp only [unit, hleadCoeff]
        rcases LawfulGcdOps.normUnit_unit c with ⟨inverse, hinverse⟩
        have hunitNe : GcdOps.normUnit c ≠ 0 := by
          intro hzero
          rw [hzero, Lean.Grind.Semiring.zero_mul] at hinverse
          exact LawfulGcdOps.one_ne_zero hinverse.symm
        have hinverse' : inverse * GcdOps.normUnit c = 1 := by
          rw [Lean.Grind.CommSemiring.mul_comm]
          exact hinverse
        have hexact : GcdOps.exactDiv 1 (GcdOps.normUnit c) = inverse := by
          have hcancel := LawfulGcdOps.exactDiv_cancel
            inverse (GcdOps.normUnit c) hunitNe
          rw [hinverse'] at hcancel
          exact hcancel
        have hunitInv : unitInv = inverse := by
          simp only [unitInv, hunit, hexact]
        have hpolyUnit : polyNormUnit primitive = C unit := by
          unfold polyNormUnit
          rw [hlead, hunit]
        have hconstant :
            (C unitInv : MvPoly n R cmp) * C unit = 1 := by
          change monomial Mono.zero unitInv * monomial Mono.zero unit = 1
          rw [monomial_mul_monomial, Mono.zero_mul, hunitInv, hunit,
            hinverse']
          rfl
        have hcancelPoly :
            (C unitInv : MvPoly n R cmp) * polyNormalize primitive =
              primitive := by
          rw [polyNormalize, hpolyUnit]
          calc
            C unitInv * (primitive * C unit) =
                (C unitInv * primitive) * C unit :=
              (MvPoly.mul_assoc ..).symm
            _ = (primitive * C unitInv) * C unit := by
              rw [MvPoly.mul_comm (C unitInv) primitive]
            _ = primitive * (C unitInv * C unit) :=
              MvPoly.mul_assoc ..
            _ = primitive * 1 := by rw [hconstant]
            _ = primitive := MvPoly.mul_one _
        have hscalar :
            (C (scalar * unitInv) : MvPoly n R cmp) =
              C scalar * C unitInv := by
          change monomial Mono.zero (scalar * unitInv) =
            monomial Mono.zero scalar * monomial Mono.zero unitInv
          rw [monomial_mul_monomial, Mono.zero_mul]
        calc
          C (scalar * unitInv) * polyNormalize primitive =
              (C scalar * C unitInv) * polyNormalize primitive := by
            rw [hscalar]
          _ = C scalar * (C unitInv * polyNormalize primitive) :=
            MvPoly.mul_assoc ..
          _ = C scalar * primitive := by rw [hcancelPoly]
          _ = p := content_mul_primPart p

omit [LawfulBezoutOps R] [GcdProducer R] in
/-- The polynomial component of the primitive split is canonical. -/
theorem sqfPrimitiveSplit_normalized [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) :
    polyNormalize (sqfPrimitiveSplit p).2 = (sqfPrimitiveSplit p).2 := by
  simp only [sqfPrimitiveSplit]
  exact polyNormalize_idem _

omit [LawfulBezoutOps R] [GcdProducer R] in
/-- A nonzero polynomial component of the split remains primitive after its
normalization unit is applied. -/
theorem sqfPrimitiveSplit_primitive [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) (hsecond : (sqfPrimitiveSplit p).2 ≠ 0) :
    content (sqfPrimitiveSplit p).2 = 1 := by
  let primitive := primPart p
  change polyNormalize primitive ≠ 0 at hsecond
  have hprimitive : primitive ≠ 0 := by
    intro hzero
    apply hsecond
    rw [hzero, polyNormalize_zero]
  have hcontentOne : content (1 : MvPoly n R cmp) = 1 := by
    have honeUnit : GcdOps.isUnit (1 : R) = true :=
      (LawfulGcdOps.isUnit_iff 1).mpr
        ⟨1, Lean.Grind.Semiring.one_mul 1⟩
    have hnormalizeOne : normalize (1 : R) = 1 :=
      LawfulGcdOps.normalize_unit 1 honeUnit
    unfold content scalarContent
    change ((match (1 : MvPoly n R cmp).termsList with
      | [] => (0 : R)
      | (_, c) :: terms =>
          normalize (terms.foldl (fun g term => GcdOps.gcd g term.2) c)) :
        R) = (1 : R)
    change ((match
      (monomial Mono.zero (1 : R) : MvPoly n R cmp).termsList with
      | [] => (0 : R)
      | (_, c) :: terms =>
          normalize (terms.foldl (fun g term => GcdOps.gcd g term.2) c)) :
        R) = (1 : R)
    rw [termsList_monomial, ite_eq_right LawfulGcdOps.one_ne_zero]
    exact hnormalizeOne
  have hunitContent : content (polyNormUnit primitive) = 1 := by
    rcases (polyIsUnit_iff (polyNormUnit primitive)).mp
        (polyNormUnit_isUnit primitive) with ⟨inverse, hinverse⟩
    have hproduct := congrArg content hinverse
    rw [content_mul, hcontentOne] at hproduct
    have hbaseUnit : GcdOps.isUnit (content (polyNormUnit primitive)) = true :=
      (LawfulGcdOps.isUnit_iff _).mpr ⟨content inverse, hproduct⟩
    calc
      content (polyNormUnit primitive) =
          normalize (content (polyNormUnit primitive)) :=
        (normalize_scalarContent _).symm
      _ = 1 := LawfulGcdOps.normalize_unit _ hbaseUnit
  have hp : p ≠ 0 := by
    intro hzero
    subst p
    exact hprimitive (by simp [primitive])
  have hprimitiveContent : content primitive = 1 := by
    simpa only [primitive] using content_primPart hp
  change content (polyNormalize primitive) = 1
  rw [polyNormalize, content_mul, hprimitiveContent,
    hunitContent, Lean.Grind.Semiring.one_mul]

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
def sqfStep [NatNoZero R] {m : Nat} (lower : SqfOpsAt R m) :
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
def sqfOps [NatNoZero R] : (m : Nat) → SqfOpsAt R m
  | 0 => sqfBase
  | m + 1 => sqfStep (sqfOps m)

omit [LawfulGcdOps R] [LawfulBezoutOps R] in
private theorem positive_sqfOps [NatNoZero R] (m : Nat)
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
private theorem sorted_sqfOps [NatNoZero R] (m : Nat)
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
def sqfDecomp [IsMonomialOrder cmp] [NatNoZero R]
    (p : MvPoly n R cmp) : SqfDecomp n R cmp :=
  (sqfOps (R := R) n).decomp cmp p

/-- Product of the distinct polynomial factors; scalar content is omitted. -/
def radical [IsMonomialOrder cmp] [NatNoZero R]
    (p : MvPoly n R cmp) : MvPoly n R cmp :=
  let q := polyNormalize (primPart p)
  if q == 0 then 0
  else quotient q (gcdList (q :: derivatives q))

/-- Exact Boolean squarefree decision under the relative CAS convention. -/
def isSquarefree [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) : Bool :=
  let q := primPart p
  polyIsUnit (gcdList (q :: derivatives q))

theorem isSquarefree_iff [IsMonomialOrder cmp]
    [Div R] [ExactDivLaws R] [Hex.Fraction.NonzeroOne R] [PerfectFrac R]
    (p : MvPoly n R cmp) :
    isSquarefree p = true ↔ Squarefree p := by
  rcases PerfectFrac.charZeroOrPerfect (R := R) with hchar | hperfect
  · let q := primPart p
    by_cases hp : p = 0
    · subst p
      simp only [isSquarefree, primPart_zero, gcdList_derivatives_zero]
      constructor
      · intro hunit
        rcases (polyIsUnit_iff (0 : MvPoly n R cmp)).mp hunit with ⟨u, hu⟩
        rw [MvPoly.zero_mul] at hu
        exact False.elim (LawfulGcdOps.one_ne_zero hu.symm)
      · intro hsq
        exact False.elim (hsq.1 rfl)
    · have hq0 : q ≠ 0 := by
        intro hzero
        apply hp
        rw [← content_mul_primPart p]
        change C (content p) * q = 0
        rw [hzero, MvPoly.mul_zero]
      letI charZero : NatNoZero R := ⟨by
        intro m hm hzero
        apply hchar m hm
        change Hex.Fraction.ofCoeff (m : R) = 0
        rw [Hex.Fraction.ofCoeff_eq_zero_iff]
        exact hzero⟩
      have hprimitive : Primitive q := by
        apply primitive_of_scalarContent_one
        change content q = 1
        exact content_primPart hp
      change polyIsUnit (gcdList (q :: derivatives q)) = true ↔ Squarefree p
      rw [gcdList_unit_iff_squarefree_charZero q hprimitive,
        squarefree_primPart p]
  · sorry

theorem radical_squarefree [IsMonomialOrder cmp] [NatNoZero R]
    (p : MvPoly n R cmp) (hp : p ≠ 0) : Squarefree (radical p) := by
  sorry

/-- The radical divides the original input, including its scalar content
and normalization unit. -/
theorem radical_dvd [IsMonomialOrder cmp] [NatNoZero R]
    (p : MvPoly n R cmp) : radical p ∣ p := by
  let q := polyNormalize (primPart p)
  have hrestore : C (sqfPrimitiveSplit p).1 * q = p :=
    sqfPrimitiveSplit_product p
  unfold radical
  change (if q == 0 then 0 else quotient q (gcdList (q :: derivatives q))) ∣ p
  by_cases hq : q = 0
  · simp only [hq, beq_self_eq_true, ite_true, mul_zero] at hrestore ⊢
    rw [← hrestore]
    exact ⟨0, (mul_zero 0).symm⟩
  · simp only [beq_iff_eq, hq, ite_false]
    have hd : gcdList (q :: derivatives q) ∣ q :=
      gcdList_dvd (List.mem_cons_self ..)
    have hd0 : gcdList (q :: derivatives q) ≠ 0 := by
      intro hzero
      rcases hd with ⟨r, hr⟩
      rw [hzero, mul_zero] at hr
      exact hq hr
    have hquot := quotient_mul_of_dvd hd0 hd
    refine ⟨C (sqfPrimitiveSplit p).1 * gcdList (q :: derivatives q), ?_⟩
    calc
      p = C (sqfPrimitiveSplit p).1 * q := hrestore.symm
      _ = (C (sqfPrimitiveSplit p).1 * gcdList (q :: derivatives q)) *
          quotient q (gcdList (q :: derivatives q)) := by
        rw [mul_assoc (C (sqfPrimitiveSplit p).1),
          mul_comm (gcdList _) (quotient ..), hquot]

omit [LawfulGcdOps R] [LawfulBezoutOps R] in
@[simp] theorem radical_zero [IsMonomialOrder cmp] [NatNoZero R] :
    radical (0 : MvPoly n R cmp) = 0 := by
  simp [radical]

/-- Multiplying the scalar and factor powers reconstructs the input. -/
theorem sqfDecomp_prod [IsMonomialOrder cmp] [NatNoZero R]
    (p : MvPoly n R cmp) :
    (sqfDecomp p).factors.foldl
      (fun acc f => acc * f.factor ^ f.multiplicity)
      (C (sqfDecomp p).content) = p := by
  sorry

/-- Every polynomial returned by square-free decomposition is square-free. -/
theorem sqfDecomp_squarefree [IsMonomialOrder cmp] [NatNoZero R]
    (p : MvPoly n R cmp) :
    ∀ f ∈ (sqfDecomp p).factors, Squarefree f.factor := by
  sorry

theorem sqfDecomp_primitive [IsMonomialOrder cmp] [NatNoZero R]
    (p : MvPoly n R cmp) :
    ∀ f ∈ (sqfDecomp p).factors, content f.factor = 1 := by
  sorry

theorem sqfDecomp_coprime [IsMonomialOrder cmp] [NatNoZero R]
    (p : MvPoly n R cmp) :
    ∀ f ∈ (sqfDecomp p).factors, ∀ g ∈ (sqfDecomp p).factors,
      f.multiplicity ≠ g.multiplicity →
        ∀ d, d ∣ f.factor → d ∣ g.factor → GcdOps.isUnit d = true := by
  sorry

omit [LawfulGcdOps R] [LawfulBezoutOps R] in
theorem sqfDecomp_multiplicity_pos [IsMonomialOrder cmp]
    [NatNoZero R] (p : MvPoly n R cmp) :
    ∀ f ∈ (sqfDecomp p).factors, 0 < f.multiplicity := by
  simpa [sqfDecomp, PositiveMultiplicities] using
    positive_sqfOps (R := R) n cmp p

omit [LawfulGcdOps R] [LawfulBezoutOps R] in
theorem sqfDecomp_multiplicity_sorted [IsMonomialOrder cmp]
    [NatNoZero R] (p : MvPoly n R cmp) :
    List.Pairwise (fun f g => f.multiplicity < g.multiplicity)
      (sqfDecomp p).factors := by
  simpa [sqfDecomp, SortedMultiplicities] using
    sorted_sqfOps (R := R) n cmp p

theorem sqfDecomp_nonconstant [IsMonomialOrder cmp]
    [NatNoZero R] (p : MvPoly n R cmp) :
    ∀ f ∈ (sqfDecomp p).factors, ¬ IsConst f.factor := by
  sorry

end Hex.MvPoly
