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

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
private theorem dvd_add_poly {a b d : MvPoly n R cmp}
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
private theorem dvd_mul_right_poly {a d : MvPoly n R cmp}
    (b : MvPoly n R cmp) (h : d ∣ a) : d ∣ a * b := by
  rcases h with ⟨x, hx⟩
  refine ⟨x * b, ?_⟩
  rw [hx]
  grind

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
private theorem dvd_mul_left_poly {a d : MvPoly n R cmp}
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
private theorem view_pow_size_lower [NatNoZero R]
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
private theorem isConst_of_all_powers_dvd [NatNoZero R]
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
private theorem content_eq_one_of_primitive
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
private theorem primitive_of_dvd_primitive [IsMonomialOrder cmp]
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
private theorem normalized_left_factor [IsMonomialOrder cmp]
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
private theorem primitive_const_normalized_eq_one [IsMonomialOrder cmp]
    {p : MvPoly n R cmp} (hp : Primitive p)
    (hconst : IsConst p) (hnormalized : polyNormalize p = p) : p = 1 := by
  have hunit := unit_of_const_dvd_primitive hp hconst
    (show p ∣ p from ⟨1, (MvPoly.one_mul p).symm⟩)
  calc
    p = polyNormalize p := hnormalized.symm
    _ = 1 := polyNormalize_unit p hunit

private theorem contentIn_one_of_dvd
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

private theorem gcd_quotients [IsMonomialOrder cmp]
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
private theorem polyNormalize_pow [IsMonomialOrder cmp]
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
private theorem mv_pow_ne_zero {p : MvPoly n R cmp} (hp : p ≠ 0) :
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
private theorem mv_one_pow :
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

private theorem isConst_of_derivatives_zero_perfect
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

private theorem gcdList_unit_iff_squarefree_of_kernel [IsMonomialOrder cmp]
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
private theorem gcdList_unit_iff_squarefree_charZero [IsMonomialOrder cmp]
    [NatNoZero R]
    (q : MvPoly n R cmp) (hprimitive : Primitive q) :
    polyIsUnit (gcdList (q :: derivatives q)) = true ↔ Squarefree q := by
  apply gcdList_unit_iff_squarefree_of_kernel q hprimitive
  intro _ g _ _ hderiv
  exact isConst_of_derivatives_zero g hderiv

private theorem powers_dvd_derivative_gcd [IsMonomialOrder cmp]
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

private def sqfProduct (factors : List (SqfFactor n R cmp)) :
    MvPoly n R cmp :=
  factors.foldl (fun acc factor =>
    acc * factor.factor ^ factor.multiplicity) 1

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
private theorem sqfProduct_from (factors : List (SqfFactor n R cmp))
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
@[simp] private theorem sqfProduct_nil :
    sqfProduct ([] : List (SqfFactor n R cmp)) = 1 := rfl

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
private theorem sqfProduct_cons (factor : SqfFactor n R cmp)
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
private theorem sqfProduct_merge_fold
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
private theorem sqfProduct_append
    (left right : List (SqfFactor n R cmp)) :
    sqfProduct (left ++ right) = sqfProduct left * sqfProduct right := by
  induction left with
  | nil => rw [List.nil_append, sqfProduct_nil, MvPoly.one_mul]
  | cons factor factors ih =>
      rw [List.cons_append, sqfProduct_cons, sqfProduct_cons, ih]
      grind

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
private theorem constIn_C
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
private theorem sqfProduct_map_constIn
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

private theorem primitive_constIn
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
private theorem isConst_of_constIn
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

private theorem squarefree_constIn
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

private theorem coprime_constIn_of_content_one
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

private theorem coprime_constIn
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

private def CoprimePoly (p q : MvPoly n R cmp) : Prop :=
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

private structure FactorProperties
    (factors : List (SqfFactor n R cmp)) : Prop where
  squarefree : ∀ factor ∈ factors, Squarefree factor.factor
  primitive : ∀ factor ∈ factors, Primitive factor.factor
  nonconstant : ∀ factor ∈ factors, ¬ IsConst factor.factor
  pairwise : factors.Pairwise fun left right =>
    CoprimePoly left.factor right.factor

private theorem properties_nil :
    FactorProperties ([] : List (SqfFactor n R cmp)) :=
  { squarefree := by simp
    primitive := by simp
    nonconstant := by simp
    pairwise := by simp }

private theorem coprime_of_mem
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

private def CrossFactors (left right : List (SqfFactor n R cmp)) : Prop :=
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

private theorem properties_merge_fold [NatNoZero R]
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

private def yunContribution [NatNoZero R] [IsMonomialOrder cmp]
    (i : Fin n) : Nat → Nat → MvPoly n R cmp → MvPoly n R cmp →
      MvPoly n R cmp
  | 0, _, _, _ => 1
  | fuel + 1, k, b, d =>
      if polyIsUnit b then 1
      else
        let factor := gcd b d
        let nextB := quotient b factor
        let nextC := quotient d factor
        let nextD := nextC - derivative i nextB
        let tail := yunContribution i fuel (k + 1) nextB nextD
        if polyIsUnit factor then tail else factor ^ k * tail

private structure YunState [NatNoZero R]
    {m : Nat} {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order] [IsMonomialOrder order]
    (i : Fin (m + 1)) (k : Nat)
    (b d target residual : MvPoly (m + 1) R order) : Prop where
  b_ne : b ≠ 0
  residual_ne : residual ≠ 0
  reconstruct : b ^ k * residual = target
  differential : d * residual = b * derivative i residual
  primitive : Primitive target
  normalized : polyNormalize target = target
  content_one : contentIn i Mono.lex residual = 1
  coprime : ∀ e, e ∣ b →
    e ∣ ((k : Nat) : MvPoly (m + 1) R order) * derivative i b + d →
      polyIsUnit e = true

private theorem yunState_step [NatNoZero R]
    {m : Nat} {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order] [IsMonomialOrder order]
    (i : Fin (m + 1)) (k : Nat)
    {b d target residual : MvPoly (m + 1) R order}
    (state : YunState i k b d target residual) :
    let factor := gcd b d
    let nextB := quotient b factor
    let nextC := quotient d factor
    let nextD := nextC - derivative i nextB
    ∃ nextTarget nextResidual,
      YunState i (k + 1) nextB nextD nextTarget nextResidual ∧
        factor ^ k * nextTarget = target := by
  let factor := gcd b d
  let nextB := quotient b factor
  let nextC := quotient d factor
  let nextD := nextC - derivative i nextB
  rcases gcd_quotients state.b_ne with
    ⟨hfactor0, hnextB, hnextC, hcoprime⟩
  have hcancelFactor :
      nextC * residual = nextB * derivative i residual := by
    have hzero : factor *
        (nextC * residual - nextB * derivative i residual) = 0 := by
      calc
        factor * (nextC * residual - nextB * derivative i residual) =
            (nextC * factor) * residual -
              (nextB * factor) * derivative i residual := by grind
        _ = d * residual - b * derivative i residual := by
          rw [hnextC, hnextB]
        _ = 0 := by rw [state.differential]; grind
    rcases GcdDomainLaws.no_zero_div factor _ hzero with hzero | hrest
    · exact False.elim (hfactor0 hzero)
    · grind
  have hnextB0 : nextB ≠ 0 := by
    intro hzero
    apply state.b_ne
    calc
      b = nextB * factor := hnextB.symm
      _ = 0 := by rw [hzero, MvPoly.zero_mul]
  have hnextBResidual : nextB ∣ residual := by
    have hcoprime' : ∀ e, e ∣ nextC → e ∣ nextB → ∃ u, e * u = 1 :=
      fun e heC heB => (polyIsUnit_iff e).mp (hcoprime e heB heC)
    have hleft : nextB ∣ residual * nextC := by
      refine ⟨derivative i residual, ?_⟩
      calc
        residual * nextC = nextC * residual := MvPoly.mul_comm ..
        _ = nextB * derivative i residual := hcancelFactor
        _ = derivative i residual * nextB := MvPoly.mul_comm ..
    have hright : nextB ∣ residual * nextB :=
      ⟨residual, rfl⟩
    exact CoprimeCancelLaws.cancel_coprime residual nextC nextB nextB
      hcoprime' hleft hright
  let nextResidual := quotient residual nextB
  have hnextResidual : nextResidual * nextB = residual :=
    quotient_mul_of_dvd hnextB0 hnextBResidual
  have hnextResidual0 : nextResidual ≠ 0 := by
    intro hzero
    apply state.residual_ne
    change residual = 0
    calc
      residual = nextResidual * nextB := hnextResidual.symm
      _ = 0 := by rw [hzero, MvPoly.zero_mul]
  have hcancelNextB :
      nextC * nextResidual =
        derivative i nextB * nextResidual +
          nextB * derivative i nextResidual := by
    have hzero : nextB *
        (nextC * nextResidual -
          (derivative i nextB * nextResidual +
            nextB * derivative i nextResidual)) = 0 := by
      calc
        nextB * (nextC * nextResidual -
            (derivative i nextB * nextResidual +
              nextB * derivative i nextResidual)) =
            nextC * (nextResidual * nextB) -
              nextB * derivative i (nextResidual * nextB) := by
          rw [derivative_mul]
          grind
        _ = nextC * residual - nextB * derivative i residual := by
          rw [hnextResidual]
        _ = 0 := by rw [hcancelFactor]; grind
    rcases GcdDomainLaws.no_zero_div nextB _ hzero with hzero | hrest
    · exact False.elim (hnextB0 hzero)
    · grind
  have hnextDifferential :
      nextD * nextResidual =
        nextB * derivative i nextResidual := by
    change (nextC - derivative i nextB) * nextResidual = _
    grind
  let nextTarget := nextB ^ (k + 1) * nextResidual
  have htarget : factor ^ k * nextTarget = target := by
    change factor ^ k * (nextB ^ (k + 1) * nextResidual) = target
    calc
      factor ^ k * (nextB ^ (k + 1) * nextResidual) =
          (nextB * factor) ^ k * (nextResidual * nextB) := by
        rw [Lean.Grind.CommSemiring.mul_pow]
        rw [MvPoly.pow_succ]
        grind
      _ = b ^ k * residual := by rw [hnextB, hnextResidual]
      _ = target := state.reconstruct
  have htarget0 : nextTarget ≠ 0 := by
    intro hzero
    have hzeroTarget : target = 0 := by
      calc
        target = factor ^ k * nextTarget := htarget.symm
        _ = 0 := by rw [hzero, MvPoly.mul_zero]
    have hstateTarget0 : target ≠ 0 := by
      intro ht
      have hz := state.reconstruct.trans ht
      rcases GcdDomainLaws.no_zero_div (b ^ k) residual hz with _ | he
      · exact (mv_pow_ne_zero state.b_ne k) ‹_›
      · exact state.residual_ne he
    exact False.elim (hstateTarget0 hzeroTarget)
  have hnextPrimitive : Primitive nextTarget := by
    apply primitive_of_dvd_primitive state.primitive
    exact ⟨factor ^ k, htarget.symm⟩
  have hfactorNormalized : polyNormalize factor = factor :=
    gcd_normalized b d
  have hfactorPowerNormalized : polyNormalize (factor ^ k) = factor ^ k :=
    polyNormalize_pow hfactorNormalized k
  have hnextNormalized : polyNormalize nextTarget = nextTarget := by
    apply normalized_left_factor state.normalized hfactorPowerNormalized
      (mv_pow_ne_zero hfactor0 k)
    rw [MvPoly.mul_comm]
    exact htarget
  have hnextContent : contentIn i Mono.lex nextResidual = 1 := by
    apply contentIn_one_of_dvd (R := R) (m := m) (order := order)
      i state.content_one
    refine ⟨nextB, ?_⟩
    calc
      residual = nextResidual * nextB := hnextResidual.symm
      _ = nextB * nextResidual := MvPoly.mul_comm ..
  have hnextCoprime : ∀ e, e ∣ nextB →
      e ∣ (((k + 1 : Nat) : MvPoly (m + 1) R order) *
          derivative i nextB + nextD) → polyIsUnit e = true := by
    intro e heB heNext
    have hnextExpression :
        (((k + 1 : Nat) : MvPoly (m + 1) R order) *
            derivative i nextB + nextD) =
          ((k : Nat) : MvPoly (m + 1) R order) *
            derivative i nextB + nextC := by
      change ((k + 1 : Nat) : MvPoly (m + 1) R order) *
          derivative i nextB + (nextC - derivative i nextB) = _
      rw [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_one]
      grind
    rw [hnextExpression] at heNext
    have heOldB : e ∣ b := by
      rcases heB with ⟨a, ha⟩
      refine ⟨a * factor, ?_⟩
      calc
        b = nextB * factor := hnextB.symm
        _ = (a * e) * factor := by rw [ha]
        _ = (a * factor) * e := by grind
    have heFirst : e ∣ factor *
        (((k : Nat) : MvPoly (m + 1) R order) *
          derivative i nextB + nextC) :=
      dvd_mul_left_poly factor heNext
    have heSecond : e ∣
        ((k : Nat) : MvPoly (m + 1) R order) * nextB *
          derivative i factor := by
      rcases heB with ⟨a, ha⟩
      refine ⟨((k : Nat) : MvPoly (m + 1) R order) * a *
          derivative i factor, ?_⟩
      rw [ha]
      grind
    have heOld : e ∣
        ((k : Nat) : MvPoly (m + 1) R order) * derivative i b + d := by
      have hsum := dvd_add_poly heFirst heSecond
      have heq :
          factor * (((k : Nat) : MvPoly (m + 1) R order) *
              derivative i nextB + nextC) +
            ((k : Nat) : MvPoly (m + 1) R order) * nextB *
              derivative i factor =
            ((k : Nat) : MvPoly (m + 1) R order) * derivative i b + d := by
        rw [← hnextB, derivative_mul, ← hnextC]
        grind
      rw [heq] at hsum
      exact hsum
    exact state.coprime e heOldB heOld
  refine ⟨nextTarget, nextResidual, ?_, htarget⟩
  exact
    { b_ne := hnextB0
      residual_ne := hnextResidual0
      reconstruct := rfl
      differential := hnextDifferential
      primitive := hnextPrimitive
      normalized := hnextNormalized
      content_one := hnextContent
      coprime := hnextCoprime }

private theorem unit_of_derivative_zero_contentIn_one [NatNoZero R]
    {m : Nat} {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order] [IsMonomialOrder order]
    (i : Fin (m + 1)) {p : MvPoly (m + 1) R order}
    (hderivative : derivative i p = 0)
    (hcontent : contentIn i Mono.lex p = 1) : polyIsUnit p = true := by
  let view := toUnivariate i Mono.lex p
  let constant := view.coeff 0
  have hviewDerivative : DensePoly.derivative view = 0 := by
    rw [← toUnivariate_derivative, hderivative, toUnivariate_zero]
  have hview : view = DensePoly.C constant := by
    apply DensePoly.ext_coeff
    intro k
    cases k with
    | zero => rw [DensePoly.coeff_C, ite_eq_left rfl]
    | succ k =>
        have hcoeff := congrArg
          (fun q : DensePoly (MvPoly m R Mono.lex) => q.coeff k)
          hviewDerivative
        rw [DensePoly.coeff_derivative_semiring, DensePoly.coeff_zero] at hcoeff
        have hcast :
            ((k + 1 : Nat) : MvPoly m R Mono.lex) ≠ 0 := by
          intro hzero
          have hzeroCoeff := congrArg (coeff Mono.zero) hzero
          rw [coeff_natCast, coeff_zero, ite_eq_left rfl] at hzeroCoeff
          exact NatNoZero.natCast_ne_zero (k + 1) (by omega) hzeroCoeff
        have hcoefficient : view.coeff (k + 1) = 0 := by
          rcases GcdDomainLaws.no_zero_div
              ((k + 1 : Nat) : MvPoly m R Mono.lex)
              (view.coeff (k + 1)) hcoeff with hzero | hzero
          · exact False.elim (hcast hzero)
          · exact hzero
        rw [DensePoly.coeff_C, ite_eq_right (by omega)]
        exact hcoefficient
  have hpConst : p = constIn (cmp := order) i Mono.lex constant := by
    calc
      p = ofUnivariate i Mono.lex view :=
        (ofUnivariate_toUnivariate i p).symm
      _ = ofUnivariate i Mono.lex (DensePoly.C constant) := by rw [hview]
      _ = constIn (cmp := order) i Mono.lex constant := rfl
  have hconstantDiv : constant ∣ contentIn i Mono.lex p := by
    apply dvd_contentIn i Mono.lex p constant
    intro k
    change constant ∣ view.coeff k
    rw [hview, DensePoly.coeff_C]
    split
    · exact ⟨1, (MvPoly.one_mul constant).symm⟩
    · exact ⟨0, (MvPoly.zero_mul constant).symm⟩
  rw [hcontent] at hconstantDiv
  rcases hconstantDiv with ⟨inverse, hinverse⟩
  apply (polyIsUnit_iff p).mpr
  refine ⟨constIn (cmp := order) i Mono.lex inverse, ?_⟩
  have hone : constant * inverse = 1 := by
    calc
      constant * inverse = inverse * constant := MvPoly.mul_comm ..
      _ = 1 := hinverse.symm
  rw [hpConst, ← constIn_mul, hone, constIn_one]

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
private theorem totalDegree_monomial_le
    (p : MvPoly n R cmp) {m : Mono n} (hm : m ∈ p.monomials) :
    Mono.degree m ≤ p.totalDegree := by
  unfold monomials at hm
  rcases List.mem_map.mp hm with ⟨term, hterm, hfirst⟩
  rcases term with ⟨k, c⟩
  simp only at hfirst
  subst k
  rw [totalDegree_eq]
  unfold foldTerms
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  have le_start (terms : List (Mono n × R)) (init : Nat) :
      init ≤ terms.foldl
        (fun d term => max d (Mono.degree term.1)) init := by
    induction terms generalizing init with
    | nil => exact Nat.le_refl _
    | cons term terms ih =>
        exact Nat.le_trans (Nat.le_max_left ..) (ih _)
  have member_bound :
      ∀ (terms : List (Mono n × R)) (init : Nat) {term},
        term ∈ terms →
          Mono.degree term.1 ≤ terms.foldl
            (fun d term => max d (Mono.degree term.1)) init := by
    intro terms init term hterm
    induction terms generalizing init with
    | nil => simp at hterm
    | cons head terms ih =>
        simp only [List.foldl_cons]
        cases List.mem_cons.mp hterm with
        | inl h =>
            subst head
            exact Nat.le_trans (Nat.le_max_right ..) (le_start terms _)
        | inr h => exact ih _ h
  exact member_bound p.termsList 0 hterm

omit [LawfulBezoutOps R] [GcdProducer R] in
private theorem view_size_le_totalDegree_succ
    {m : Nat} {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order] [IsMonomialOrder order]
    (i : Fin (m + 1)) (p : MvPoly (m + 1) R order) :
    (toUnivariate i Mono.lex p).size ≤ p.totalDegree + 1 := by
  let view := toUnivariate i Mono.lex p
  by_cases hsize : view.size = 0
  · change view.size ≤ p.totalDegree + 1
    omega
  have hpos : 0 < view.size := Nat.pos_of_ne_zero hsize
  have hleading0 : view.leadingCoeff ≠ (0 : MvPoly m R Mono.lex) :=
    DensePoly.leadingCoeff_ne_zero_of_pos_size view hpos
  cases hterm : view.leadingCoeff.leadingTerm with
  | none =>
      exact False.elim
        (hleading0 ((leadingTerm_eq_none_iff view.leadingCoeff).mp hterm))
  | some term =>
      rcases term with ⟨monomial, coefficient⟩
      have hcoefficient0 : coefficient ≠ 0 := by
        intro hzero
        have hstored :=
          (leadingTerm_eq_some_iff view.leadingCoeff monomial coefficient).mp
            hterm |>.1
        subst coefficient
        exact (view.leadingCoeff.coeff?_ne_zero monomial) hstored
      have hsourceCoeff :
          coeff (insertVar i (view.size - 1) monomial) p = coefficient := by
        rw [← toUnivariate_coeff (cmp' := Mono.lex) i p]
        change coeff monomial (view.coeff (view.size - 1)) = coefficient
        rw [← DensePoly.leadingCoeff_eq_coeff_last view hpos]
        exact coeff_eq_of_leadingTerm hterm
      have hsourceMem :
          insertVar i (view.size - 1) monomial ∈ p.monomials :=
        (mem_monomials_iff _ p).mpr (hsourceCoeff ▸ hcoefficient0)
      have htotal := totalDegree_monomial_le p hsourceMem
      have hcoordinate :=
        Mono.degreeOf_le_degree i (insertVar i (view.size - 1) monomial)
      rw [degreeOf_insertVar] at hcoordinate
      change view.size ≤ p.totalDegree + 1
      omega

omit [LawfulBezoutOps R] [GcdProducer R] in
private theorem exponent_le_totalDegree_of_pow_dvd [NatNoZero R]
    {m : Nat} {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order] [IsMonomialOrder order]
    {source b : MvPoly (m + 1) R order} {k : Nat}
    (hsource : source ≠ 0) (hconst : ¬ IsConst b) (hk : 0 < k)
    (hdiv : b ^ k ∣ source) : k ≤ source.totalDegree := by
  have hb0 : b ≠ 0 := by
    intro hzero
    apply hconst
    subst b
    simp [IsConst]
  have hvars : b.vars ≠ [] := hconst
  cases hvarsEq : b.vars with
  | nil => exact False.elim (hvars hvarsEq)
  | cons i tail =>
      have hi : i ∈ b.vars := by rw [hvarsEq]; simp
      have hpowerLower := view_pow_size_lower i b hi (k - 1)
      have hkPower : k - 1 + 1 = k := by omega
      rw [hkPower] at hpowerLower
      rcases hdiv with ⟨q, hq⟩
      have hq0 : q ≠ 0 := by
        intro hzero
        apply hsource
        rw [hq, hzero, MvPoly.zero_mul]
      have hqView : toUnivariate i Mono.lex q ≠ 0 := by
        intro hzero
        apply hq0
        calc
          q = ofUnivariate i Mono.lex (toUnivariate i Mono.lex q) :=
            (ofUnivariate_toUnivariate i q).symm
          _ = 0 := by rw [hzero]; rfl
      have hpower0 : b ^ k ≠ 0 := mv_pow_ne_zero hb0 k
      have hpowerView : toUnivariate i Mono.lex (b ^ k) ≠ 0 := by
        intro hzero
        apply hpower0
        calc
          b ^ k = ofUnivariate i Mono.lex
              (toUnivariate i Mono.lex (b ^ k)) :=
            (ofUnivariate_toUnivariate i (b ^ k)).symm
          _ = 0 := by rw [hzero]; rfl
      have hqPos : 0 < (toUnivariate i Mono.lex q).size :=
        Nat.pos_of_ne_zero
          (fun h => hqView ((DensePoly.size_eq_zero_iff _).mp h))
      have hpowerPos : 0 < (toUnivariate i Mono.lex (b ^ k)).size :=
        Nat.pos_of_ne_zero
          (fun h => hpowerView ((DensePoly.size_eq_zero_iff _).mp h))
      have htop :
          (toUnivariate i Mono.lex q).leadingCoeff *
              (toUnivariate i Mono.lex (b ^ k)).leadingCoeff ≠
            (0 : MvPoly m R Mono.lex) := by
        intro hzero
        rcases GcdDomainLaws.no_zero_div _ _ hzero with hl | hr
        · exact (DensePoly.leadingCoeff_ne_zero_of_pos_size _ hqPos) hl
        · exact (DensePoly.leadingCoeff_ne_zero_of_pos_size _ hpowerPos) hr
      have hproduct := DensePoly.size_mul_of_top_ne
        (toUnivariate i Mono.lex q) (toUnivariate i Mono.lex (b ^ k))
        hqPos hpowerPos htop
      have hviewEq := congrArg
        (fun f => (toUnivariate i Mono.lex f).size) hq
      rw [toUnivariate_mul, hproduct] at hviewEq
      have hsourceUpper := view_size_le_totalDegree_succ i source
      omega

private theorem yunState_terminal [NatNoZero R]
    {m : Nat} {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order] [IsMonomialOrder order]
    (i : Fin (m + 1)) (k : Nat)
    {b d target residual : MvPoly (m + 1) R order}
    (state : YunState i k b d target residual)
    (hunit : polyIsUnit b = true) : target = 1 := by
  rcases (polyIsUnit_iff b).mp hunit with ⟨u, hu⟩
  have hresidualDvd : residual ∣ derivative i residual := by
    refine ⟨u * d, ?_⟩
    calc
      derivative i residual = 1 * derivative i residual :=
        (MvPoly.one_mul _).symm
      _ = (b * u) * derivative i residual := by rw [hu]
      _ = u * (b * derivative i residual) := by grind
      _ = u * (d * residual) := by rw [state.differential]
      _ = (u * d) * residual := by grind
  have hderivative : derivative i residual = 0 :=
    derivative_eq_zero_of_dvd i residual state.residual_ne hresidualDvd
  have hresidualUnit : polyIsUnit residual = true :=
    unit_of_derivative_zero_contentIn_one i hderivative state.content_one
  rcases (polyIsUnit_iff residual).mp hresidualUnit with ⟨v, hv⟩
  have honePow : ∀ j : Nat, (1 : MvPoly (m + 1) R order) ^ j = 1 := by
    intro j
    induction j with
    | zero => exact MvPoly.pow_zero 1
    | succ j ih => rw [MvPoly.pow_succ, ih, MvPoly.one_mul]
  have hpower : b ^ k * u ^ k = 1 := by
    calc
      b ^ k * u ^ k = (b * u) ^ k :=
        (Lean.Grind.CommSemiring.mul_pow b u k).symm
      _ = 1 := by
        rw [hu]
        exact honePow k
  have htargetUnit : polyIsUnit target = true := by
    apply (polyIsUnit_iff target).mpr
    refine ⟨v * u ^ k, ?_⟩
    calc
      target * (v * u ^ k) =
          (b ^ k * residual) * (v * u ^ k) := by
        rw [state.reconstruct]
      _ = (b ^ k * u ^ k) * (residual * v) := by grind
      _ = 1 := by rw [hpower, hv, MvPoly.one_mul]
  calc
    target = polyNormalize target := state.normalized.symm
    _ = 1 := polyNormalize_unit target htargetUnit

private theorem yunContribution_correct [NatNoZero R]
    {m : Nat} {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order] [IsMonomialOrder order]
    (i : Fin (m + 1)) (source : MvPoly (m + 1) R order)
    (hsource : source ≠ 0) :
    ∀ fuel k b d target residual,
      0 < k → target ∣ source → source.totalDegree < k + fuel →
      YunState i k b d target residual →
        yunContribution i fuel k b d = target := by
  intro fuel
  induction fuel with
  | zero =>
      intro k b d target residual hk htargetSource hbound state
      rw [yunContribution]
      by_cases hunit : polyIsUnit b = true
      · exact (yunState_terminal i k state hunit).symm
      · exfalso
        have hconst : ¬ IsConst b := by
          intro hconst
          have hbDvdTarget : b ∣ target := by
            refine ⟨b ^ (k - 1) * residual, ?_⟩
            calc
              target = b ^ k * residual := state.reconstruct.symm
              _ = (b ^ (k - 1) * residual) * b := by
                rw [show k = k - 1 + 1 by omega, MvPoly.pow_succ]
                grind
          exact hunit (unit_of_const_dvd_primitive state.primitive hconst
            hbDvdTarget)
        have hpowerTarget : b ^ k ∣ target := by
          refine ⟨residual, ?_⟩
          calc
            target = b ^ k * residual := state.reconstruct.symm
            _ = residual * b ^ k := MvPoly.mul_comm ..
        rcases htargetSource with ⟨a, ha⟩
        rcases hpowerTarget with ⟨r, hr⟩
        have hpowerSource : b ^ k ∣ source := by
          refine ⟨a * r, ?_⟩
          calc
            source = a * target := ha
            _ = a * (r * b ^ k) := by rw [hr]
            _ = (a * r) * b ^ k := by grind
        have hdegree := exponent_le_totalDegree_of_pow_dvd
          hsource hconst hk hpowerSource
        omega
  | succ fuel ih =>
      intro k b d target residual hk htargetSource hbound state
      simp only [yunContribution]
      by_cases hunitB : polyIsUnit b = true
      · rw [if_pos hunitB]
        exact (yunState_terminal i k state hunitB).symm
      · rw [if_neg hunitB]
        let factor := gcd b d
        let nextB := quotient b factor
        let nextC := quotient d factor
        let nextD := nextC - derivative i nextB
        rcases yunState_step i k state with
          ⟨nextTarget, nextResidual, nextState, hfactorTarget⟩
        change factor ^ k * nextTarget = target at hfactorTarget
        have hnextTargetSource : nextTarget ∣ source := by
          rcases htargetSource with ⟨a, ha⟩
          refine ⟨a * factor ^ k, ?_⟩
          calc
            source = a * target := ha
            _ = a * (factor ^ k * nextTarget) := by rw [hfactorTarget]
            _ = (a * factor ^ k) * nextTarget := by grind
        have hnextBound : source.totalDegree < (k + 1) + fuel := by
          omega
        have htail :
            yunContribution i fuel (k + 1) nextB nextD = nextTarget :=
          ih (k + 1) nextB nextD nextTarget nextResidual (by omega)
            hnextTargetSource hnextBound nextState
        change
          (if polyIsUnit factor then
            yunContribution i fuel (k + 1) nextB nextD
          else factor ^ k * yunContribution i fuel (k + 1) nextB nextD) =
            target
        by_cases hunitFactor : polyIsUnit factor = true
        · rw [if_pos hunitFactor, htail]
          have hfactorOne : factor = 1 := by
            calc
              factor = polyNormalize factor := (gcd_normalized b d).symm
              _ = 1 := polyNormalize_unit factor hunitFactor
          rw [hfactorOne] at hfactorTarget
          rw [mv_one_pow, MvPoly.one_mul] at hfactorTarget
          exact hfactorTarget
        · rw [if_neg hunitFactor, htail, hfactorTarget]

omit [LawfulGcdOps R] [LawfulBezoutOps R] in
private theorem yunLoop_product [NatNoZero R] [IsMonomialOrder cmp]
    (i : Fin n) (fuel k : Nat) (b d : MvPoly n R cmp)
    (acc : List (SqfFactor n R cmp)) :
    sqfProduct (yunLoop i fuel k b d acc) =
      sqfProduct acc.reverse * yunContribution i fuel k b d := by
  induction fuel generalizing k b d acc with
  | zero =>
      rw [yunLoop, yunContribution, MvPoly.mul_one]
  | succ fuel ih =>
      simp only [yunLoop, yunContribution]
      split
      · rw [MvPoly.mul_one]
      · split
        · rw [ih]
        · rename_i hfactor
          rw [ih]
          rw [List.reverse_cons, sqfProduct_append, sqfProduct_cons,
            sqfProduct_nil, MvPoly.mul_one]
          grind

omit [LawfulGcdOps R] [LawfulBezoutOps R] in
private theorem yunLoop_acc [NatNoZero R] [IsMonomialOrder cmp]
    (i : Fin n) (fuel k : Nat) (b d : MvPoly n R cmp)
    (acc : List (SqfFactor n R cmp)) :
    yunLoop i fuel k b d acc = acc.reverse ++ yunLoop i fuel k b d [] := by
  induction fuel generalizing k b d acc with
  | zero => simp [yunLoop]
  | succ fuel ih =>
      simp only [yunLoop]
      split
      · simp
      · split
        · rw [ih]
        · rw [ih]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
            List.append_assoc]
          symm
          rw [ih]
          simp

private structure YunEntryProps
    {m : Nat} {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    (factor nextB b : MvPoly (m + 1) R order) : Prop where
  squarefree : Squarefree factor
  primitive : Primitive factor
  nonconstant : ¬ IsConst factor
  divides : factor ∣ b
  coprime_next : ∀ e, e ∣ factor → e ∣ nextB → polyIsUnit e = true

private theorem yunEntryProps [NatNoZero R]
    {m : Nat} {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order] [IsMonomialOrder order]
    (i : Fin (m + 1)) (k : Nat)
    {b d target residual : MvPoly (m + 1) R order}
    (state : YunState i k b d target residual) (hk : 0 < k)
    (hnonunit : polyIsUnit (gcd b d) ≠ true) :
    YunEntryProps (gcd b d) (quotient b (gcd b d)) b := by
  let factor := gcd b d
  let nextB := quotient b factor
  let nextC := quotient d factor
  rcases gcd_quotients state.b_ne with
    ⟨hfactor0, hnextB, hnextC, _⟩
  change factor ≠ 0 at hfactor0
  change nextB * factor = b at hnextB
  change nextC * factor = d at hnextC
  have hfactorB : factor ∣ b := gcd_dvd_left b d
  have hbTarget : b ∣ target := by
    refine ⟨b ^ (k - 1) * residual, ?_⟩
    calc
      target = b ^ k * residual := state.reconstruct.symm
      _ = (b ^ (k - 1) * residual) * b := by
        rw [show k = k - 1 + 1 by omega, MvPoly.pow_succ]
        grind
  have hfactorTarget : factor ∣ target := Hex.dvdTrans hfactorB hbTarget
  have hfactorPrimitive : Primitive factor :=
    primitive_of_dvd_primitive state.primitive hfactorTarget
  have hfactorNonconstant : ¬ IsConst factor := by
    intro hconst
    exact hnonunit
      (unit_of_const_dvd_primitive state.primitive hconst hfactorTarget)
  have hfactorSquarefree : Squarefree factor := by
    refine ⟨hfactor0, ?_⟩
    intro e heSquare
    have heFactor : e ∣ factor := by
      rcases heSquare with ⟨a, ha⟩
      refine ⟨a * e, ?_⟩
      calc
        factor = a * (e * e) := ha
        _ = (a * e) * e := by grind
    have heDerivative : e ∣ derivative i factor :=
      derivative_dvd_of_square_dvd i heSquare
    have heB : e ∣ b := Hex.dvdTrans heFactor hfactorB
    have heDerivativeB : e ∣ derivative i b := by
      rw [← hnextB, derivative_mul]
      apply dvd_add_poly
      · exact dvd_mul_left_poly (derivative i nextB) heFactor
      · exact dvd_mul_left_poly nextB heDerivative
    have heD : e ∣ d := by
      exact Hex.dvdTrans heFactor (gcd_dvd_right b d)
    have heExpression : e ∣
        ((k : Nat) : MvPoly (m + 1) R order) * derivative i b + d :=
      dvd_add_poly
        (dvd_mul_left_poly
          ((k : Nat) : MvPoly (m + 1) R order) heDerivativeB)
        heD
    exact isConst_of_unit e (state.coprime e heB heExpression)
  have hfactorNext : ∀ e, e ∣ factor → e ∣ nextB →
      polyIsUnit e = true := by
    intro e heFactor heNextB
    have heB : e ∣ b := Hex.dvdTrans heFactor hfactorB
    have heDerivativeB : e ∣ derivative i b := by
      rw [← hnextB, derivative_mul]
      apply dvd_add_poly
      · exact dvd_mul_left_poly (derivative i nextB) heFactor
      · exact dvd_mul_right_poly (derivative i factor) heNextB
    have heD : e ∣ d :=
      Hex.dvdTrans heFactor (gcd_dvd_right b d)
    have heExpression : e ∣
        ((k : Nat) : MvPoly (m + 1) R order) * derivative i b + d :=
      dvd_add_poly
        (dvd_mul_left_poly
          ((k : Nat) : MvPoly (m + 1) R order) heDerivativeB)
        heD
    exact state.coprime e heB heExpression
  exact
    { squarefree := hfactorSquarefree
      primitive := hfactorPrimitive
      nonconstant := hfactorNonconstant
      divides := hfactorB
      coprime_next := hfactorNext }

private structure YunFactors
    {n : Nat} {order : Mono n → Mono n → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    (root : MvPoly n R order) (factors : List (SqfFactor n R order)) : Prop where
  squarefree : ∀ factor ∈ factors, Squarefree factor.factor
  primitive : ∀ factor ∈ factors, Primitive factor.factor
  nonconstant : ∀ factor ∈ factors, ¬ IsConst factor.factor
  divides : ∀ factor ∈ factors, factor.factor ∣ root
  pairwise : factors.Pairwise fun left right =>
    ∀ d, d ∣ left.factor → d ∣ right.factor → polyIsUnit d = true

private theorem yunLoop_properties [NatNoZero R]
    {m : Nat} {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order] [IsMonomialOrder order]
    (i : Fin (m + 1)) :
    ∀ (fuel k : Nat)
      (b d target residual : MvPoly (m + 1) R order),
      0 < k → YunState i k b d target residual →
        YunFactors b (yunLoop i fuel k b d []) := by
  intro fuel
  induction fuel with
  | zero =>
      intro k b d target residual hk state
      simp only [yunLoop]
      exact
        { squarefree := by simp
          primitive := by simp
          nonconstant := by simp
          divides := by simp
          pairwise := by simp }
  | succ fuel ih =>
      intro k b d target residual hk state
      by_cases hunitB : polyIsUnit b = true
      · rw [yunLoop, if_pos hunitB]
        exact
          { squarefree := by simp
            primitive := by simp
            nonconstant := by simp
            divides := by simp
            pairwise := by simp }
      · let factor := gcd b d
        let nextB := quotient b factor
        let nextC := quotient d factor
        let nextD := nextC - derivative i nextB
        rcases yunState_step i k state with
          ⟨nextTarget, nextResidual, nextState, _⟩
        have htail := ih (k + 1) nextB nextD nextTarget nextResidual
          (by omega) nextState
        have hnextBdiv : nextB ∣ b := by
          have hnextBEq : nextB * factor = b :=
            (gcd_quotients state.b_ne).2.1
          refine ⟨factor, ?_⟩
          calc
            b = nextB * factor := hnextBEq.symm
            _ = factor * nextB := MvPoly.mul_comm ..
        by_cases hunitFactor : polyIsUnit factor = true
        · rw [yunLoop, if_neg hunitB]
          change YunFactors b (yunLoop i fuel (k + 1) nextB nextD
            (if polyIsUnit factor then [] else
              [{ factor := factor, multiplicity := k }]))
          rw [if_pos hunitFactor]
          exact
            { squarefree := htail.squarefree
              primitive := htail.primitive
              nonconstant := htail.nonconstant
              divides := by
                intro entry hentry
                exact Hex.dvdTrans (htail.divides entry hentry) hnextBdiv
              pairwise := htail.pairwise }
        · have hentry := yunEntryProps i k state hk hunitFactor
          let entry : SqfFactor (m + 1) R order :=
            { factor := factor, multiplicity := k }
          have hloop :
              yunLoop i (fuel + 1) k b d [] =
                entry :: yunLoop i fuel (k + 1) nextB nextD [] := by
            rw [yunLoop, if_neg hunitB]
            change yunLoop i fuel (k + 1) nextB nextD
              (if polyIsUnit factor then [] else
                [{ factor := factor, multiplicity := k }]) = _
            rw [if_neg hunitFactor, yunLoop_acc]
            simp [entry]
          rw [hloop]
          exact
            { squarefree := by
                intro candidate hcandidate
                simp only [List.mem_cons] at hcandidate
                rcases hcandidate with rfl | hcandidate
                · exact hentry.squarefree
                · exact htail.squarefree candidate hcandidate
              primitive := by
                intro candidate hcandidate
                simp only [List.mem_cons] at hcandidate
                rcases hcandidate with rfl | hcandidate
                · exact hentry.primitive
                · exact htail.primitive candidate hcandidate
              nonconstant := by
                intro candidate hcandidate
                simp only [List.mem_cons] at hcandidate
                rcases hcandidate with rfl | hcandidate
                · exact hentry.nonconstant
                · exact htail.nonconstant candidate hcandidate
              divides := by
                intro candidate hcandidate
                simp only [List.mem_cons] at hcandidate
                rcases hcandidate with rfl | hcandidate
                · exact hentry.divides
                · exact Hex.dvdTrans (htail.divides candidate hcandidate)
                    hnextBdiv
              pairwise := by
                apply List.Pairwise.cons
                · intro candidate hcandidate common hcommonEntry
                    hcommonCandidate
                  exact hentry.coprime_next common hcommonEntry
                    (Hex.dvdTrans hcommonCandidate
                      (htail.divides candidate hcandidate))
                · exact htail.pairwise }

private theorem yunInitialState [NatNoZero R]
    {m : Nat} {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order] [IsMonomialOrder order]
    (i : Fin (m + 1)) {p : MvPoly (m + 1) R order}
    (hp0 : p ≠ 0) (hprimitive : Primitive p)
    (hnormalized : polyNormalize p = p)
    (hcontent : contentIn i Mono.lex p = 1) :
    let deriv := derivative i p
    let repeated := gcd p deriv
    let b := quotient p repeated
    let c := quotient deriv repeated
    let d := c - derivative i b
    YunState i 1 b d p repeated := by
  let deriv := derivative i p
  let repeated := gcd p deriv
  let b := quotient p repeated
  let c := quotient deriv repeated
  let d := c - derivative i b
  rcases gcd_quotients hp0 with ⟨hrepeated0, hb, hc, hcoprime⟩
  change repeated ≠ 0 at hrepeated0
  change b * repeated = p at hb
  change c * repeated = deriv at hc
  have hb0 : b ≠ 0 := by
    intro hzero
    apply hp0
    rw [← hb, hzero, MvPoly.zero_mul]
  refine
    { b_ne := hb0
      residual_ne := hrepeated0
      reconstruct := ?_
      differential := ?_
      primitive := hprimitive
      normalized := hnormalized
      content_one := ?_
      coprime := ?_ }
  · rw [MvPoly.pow_succ, MvPoly.pow_zero, MvPoly.one_mul, hb]
  · change (c - derivative i b) * repeated =
      b * derivative i repeated
    calc
      (c - derivative i b) * repeated =
          c * repeated - derivative i b * repeated := by grind
      _ = deriv - derivative i b * repeated := by rw [hc]
      _ = derivative i (b * repeated) -
          derivative i b * repeated := by rw [hb]
      _ = b * derivative i repeated := by rw [derivative_mul]; grind
  · exact contentIn_one_of_dvd i hcontent (gcd_dvd_left p deriv)
  · intro e heB heExpression
    apply hcoprime e heB
    have hexpressionEq :
        (((1 : Nat) : MvPoly (m + 1) R order) * derivative i b + d) =
          c := by
      change (((1 : Nat) : MvPoly (m + 1) R order) *
        derivative i b + (c - derivative i b)) = c
      rw [Lean.Grind.Semiring.natCast_one, MvPoly.one_mul]
      grind
    rw [hexpressionEq] at heExpression
    exact heExpression

private theorem yunInitialProperties [NatNoZero R]
    {m : Nat} {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order] [IsMonomialOrder order]
    (i : Fin (m + 1)) {p : MvPoly (m + 1) R order}
    (hp0 : p ≠ 0) (hprimitive : Primitive p)
    (hnormalized : polyNormalize p = p)
    (hcontent : contentIn i Mono.lex p = 1) :
    let deriv := derivative i p
    let repeated := gcd p deriv
    let b := quotient p repeated
    let c := quotient deriv repeated
    let d := c - derivative i b
    let factors := yunLoop i (p.totalDegree + 1) 1 b d []
    FactorProperties factors ∧
      ∀ factor ∈ factors, contentIn i Mono.lex factor.factor = 1 := by
  let deriv := derivative i p
  let repeated := gcd p deriv
  let b := quotient p repeated
  let c := quotient deriv repeated
  let d := c - derivative i b
  let factors := yunLoop i (p.totalDegree + 1) 1 b d []
  have hstate : YunState i 1 b d p repeated :=
    yunInitialState i hp0 hprimitive hnormalized hcontent
  have hyun : YunFactors b factors :=
    yunLoop_properties i (p.totalDegree + 1) 1 b d p repeated
      (by omega) hstate
  have hbP : b ∣ p := by
    have hb := (gcd_quotients (b := p) (d := deriv) hp0).2.1
    change b * repeated = p at hb
    exact ⟨repeated, by rw [MvPoly.mul_comm]; exact hb.symm⟩
  refine ⟨?_, ?_⟩
  · exact
      { squarefree := hyun.squarefree
        primitive := hyun.primitive
        nonconstant := hyun.nonconstant
        pairwise := hyun.pairwise }
  · intro factor hfactor
    apply contentIn_one_of_dvd i hcontent
    exact Hex.dvdTrans (hyun.divides factor hfactor) hbP

private theorem liftProperties
    {m : Nat}
    {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    {lowerOrder : Mono m → Mono m → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    [Std.TransCmp lowerOrder] [Std.LawfulEqCmp lowerOrder]
    [IsMonomialOrder order] [IsMonomialOrder lowerOrder]
    (i : Fin (m + 1)) {factors : List (SqfFactor m R lowerOrder)}
    (hprops : FactorProperties factors) :
    FactorProperties (factors.map fun factor =>
      { factor := constIn (cmp := order) i lowerOrder factor.factor
        multiplicity := factor.multiplicity }) := by
  let lift : SqfFactor m R lowerOrder → SqfFactor (m + 1) R order :=
    fun factor =>
      { factor := constIn (cmp := order) i lowerOrder factor.factor
        multiplicity := factor.multiplicity }
  have hpairwise : (factors.map lift).Pairwise fun left right =>
      CoprimePoly left.factor right.factor := by
    induction factors with
    | nil => simp
    | cons head tail ih =>
        have hsource := List.pairwise_cons.mp hprops.pairwise
        rw [List.map_cons]
        apply List.Pairwise.cons
        · intro lifted hlifted
          rcases List.mem_map.mp hlifted with ⟨factor, hfactor, rfl⟩
          apply coprime_constIn i
          · exact (hprops.squarefree head (by simp)).1
          · exact hsource.1 factor hfactor
        · apply ih
          exact
            { squarefree := by
                intro factor hfactor
                exact hprops.squarefree factor (by simp [hfactor])
              primitive := by
                intro factor hfactor
                exact hprops.primitive factor (by simp [hfactor])
              nonconstant := by
                intro factor hfactor
                exact hprops.nonconstant factor (by simp [hfactor])
              pairwise := hsource.2 }
  change FactorProperties (factors.map lift)
  exact
    { squarefree := by
        intro lifted hlifted
        rcases List.mem_map.mp hlifted with ⟨factor, hfactor, rfl⟩
        exact squarefree_constIn i (hprops.squarefree factor hfactor)
      primitive := by
        intro lifted hlifted
        rcases List.mem_map.mp hlifted with ⟨factor, hfactor, rfl⟩
        exact primitive_constIn i (hprops.primitive factor hfactor)
      nonconstant := by
        intro lifted hlifted hconst
        rcases List.mem_map.mp hlifted with ⟨factor, hfactor, rfl⟩
        exact hprops.nonconstant factor hfactor (isConst_of_constIn i hconst)
      pairwise := hpairwise }

private theorem cross_lift_main
    {m : Nat}
    {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    {lowerOrder : Mono m → Mono m → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    [Std.TransCmp lowerOrder] [Std.LawfulEqCmp lowerOrder]
    [IsMonomialOrder order] [IsMonomialOrder lowerOrder]
    (i : Fin (m + 1)) {lower : List (SqfFactor m R lowerOrder)}
    {main : List (SqfFactor (m + 1) R order)}
    (hlower : FactorProperties lower)
    (hmain : ∀ factor ∈ main,
      contentIn i lowerOrder factor.factor = 1) :
    CrossFactors (lower.map fun factor =>
      { factor := constIn (cmp := order) i lowerOrder factor.factor
        multiplicity := factor.multiplicity }) main := by
  intro lifted hlifted mainFactor hmainFactor
  rcases List.mem_map.mp hlifted with ⟨factor, hfactor, rfl⟩
  exact coprime_constIn_of_content_one i
    (hlower.squarefree factor hfactor).1 (hmain mainFactor hmainFactor)

private theorem yunLoop_product_initial [NatNoZero R]
    {m : Nat} {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order] [IsMonomialOrder order]
    (i : Fin (m + 1)) {p : MvPoly (m + 1) R order}
    (hp0 : p ≠ 0) (hprimitive : Primitive p)
    (hnormalized : polyNormalize p = p)
    (hcontent : contentIn i Mono.lex p = 1) :
    let deriv := derivative i p
    let repeated := gcd p deriv
    let b := quotient p repeated
    let c := quotient deriv repeated
    let d := c - derivative i b
    sqfProduct (yunLoop i (p.totalDegree + 1) 1 b d []) = p := by
  let deriv := derivative i p
  let repeated := gcd p deriv
  let b := quotient p repeated
  let c := quotient deriv repeated
  let d := c - derivative i b
  have hstate : YunState i 1 b d p repeated :=
    yunInitialState i hp0 hprimitive hnormalized hcontent
  have hcontribution :
      yunContribution i (p.totalDegree + 1) 1 b d = p := by
    apply yunContribution_correct i p hp0
    · omega
    · exact ⟨1, (MvPoly.one_mul p).symm⟩
    · omega
    · exact hstate
  have hloop := yunLoop_product i (p.totalDegree + 1) 1 b d []
  rw [List.reverse_nil, sqfProduct_nil, MvPoly.one_mul, hcontribution] at hloop
  exact hloop

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
          let rawMainPart := primPartIn i Mono.lex q
          let mainSplit := sqfPrimitiveSplit rawMainPart
          let mainScalar := mainSplit.1
          let mainPart := mainSplit.2
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
          ⟨scalar * coefficientDecomp.content * mainScalar, factors⟩

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

private theorem properties_sqfOps [NatNoZero R] (m : Nat)
    (order : Mono m → Mono m → Ordering) [IsMonomialOrder order]
    (p : MvPoly m R order) :
    FactorProperties ((sqfOps (R := R) m).decomp order p).factors := by
  induction m with
  | zero =>
      simpa [sqfOps, sqfBase, sqfPrimitiveSplit] using
        (properties_nil (R := R) (cmp := order))
  | succ m ih =>
      simp only [sqfOps, sqfStep]
      split
      · exact properties_nil
      · have hq0 : (sqfPrimitiveSplit p).2 ≠ 0 := by
          intro hzero
          rename_i hterminal
          rw [hzero] at hterminal
          simp at hterminal
        cases hvars : (sqfPrimitiveSplit p).2.vars with
        | nil => exact properties_nil
        | cons i tail =>
            let q := (sqfPrimitiveSplit p).2
            let coefficientPart := contentIn i Mono.lex q
            let coefficientDecomp :=
              (sqfOps (R := R) m).decomp Mono.lex coefficientPart
            let rawMainPart := primPartIn i Mono.lex q
            let mainSplit := sqfPrimitiveSplit rawMainPart
            let mainPart := mainSplit.2
            let deriv := derivative i mainPart
            let repeated := gcd mainPart deriv
            let b := quotient mainPart repeated
            let c := quotient deriv repeated
            let d := c - derivative i b
            let mainFactors :=
              yunLoop i (mainPart.totalDegree + 1) 1 b d []
            let liftedFactors : List (SqfFactor (m + 1) R order) :=
              coefficientDecomp.factors.map fun factor =>
              { factor := constIn (cmp := order) i Mono.lex factor.factor
                multiplicity := factor.multiplicity }
            have hlower : FactorProperties coefficientDecomp.factors := by
              exact ih Mono.lex coefficientPart
            have hlifted : FactorProperties liftedFactors := by
              exact liftProperties i hlower
            have hqRestore :
                constIn i Mono.lex coefficientPart * rawMainPart = q :=
              contentIn_mul_primPartIn i Mono.lex q
            have hraw0 : rawMainPart ≠ 0 := by
              intro hzero
              apply hq0
              change q = 0
              rw [← hqRestore, hzero, MvPoly.mul_zero]
            have hmainRestore :
                (C mainSplit.1 : MvPoly (m + 1) R order) * mainPart =
                  rawMainPart := sqfPrimitiveSplit_product rawMainPart
            have hmain0 : mainPart ≠ 0 := by
              intro hzero
              apply hraw0
              rw [← hmainRestore, hzero, MvPoly.mul_zero]
            have hmainPrimitive : Primitive mainPart := by
              apply primitive_of_scalarContent_one
              exact sqfPrimitiveSplit_primitive rawMainPart hmain0
            have hmainContent : contentIn i Mono.lex mainPart = 1 := by
              have hrawContent : contentIn i Mono.lex rawMainPart = 1 :=
                primPartIn_content i Mono.lex hq0
              apply contentIn_one_of_dvd i hrawContent
              exact ⟨C mainSplit.1, hmainRestore.symm⟩
            have hmain := yunInitialProperties i hmain0 hmainPrimitive
              (sqfPrimitiveSplit_normalized rawMainPart) hmainContent
            change FactorProperties
              (liftedFactors.foldl
                (fun acc factor => mergeSqfFactor factor acc) mainFactors)
            apply properties_merge_fold liftedFactors mainFactors
            · exact hlifted
            · exact hmain.1
            · exact cross_lift_main i hlower hmain.2

private theorem split_content_of_zero [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) (hzero : (sqfPrimitiveSplit p).2 = 0) :
    C (sqfPrimitiveSplit p).1 = p := by
  have hrestore := sqfPrimitiveSplit_product p
  rw [hzero, MvPoly.mul_zero] at hrestore
  subst p
  simp [sqfPrimitiveSplit]
  rw [Lean.Grind.Semiring.zero_mul]
  exact C_zero

private theorem split_content_of_unit [IsMonomialOrder cmp]
    (p : MvPoly n R cmp)
    (hunit : polyIsUnit (sqfPrimitiveSplit p).2 = true) :
    C (sqfPrimitiveSplit p).1 = p := by
  have hnormalized := sqfPrimitiveSplit_normalized p
  have hone : (sqfPrimitiveSplit p).2 = 1 := by
    calc
      (sqfPrimitiveSplit p).2 =
          polyNormalize (sqfPrimitiveSplit p).2 := hnormalized.symm
      _ = 1 := polyNormalize_unit _ hunit
  have hrestore := sqfPrimitiveSplit_product p
  rw [hone, MvPoly.mul_one] at hrestore
  exact hrestore

private theorem split_content_of_const [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) (hzero : (sqfPrimitiveSplit p).2 ≠ 0)
    (hconst : IsConst (sqfPrimitiveSplit p).2) :
    C (sqfPrimitiveSplit p).1 = p := by
  have hprimitive : Primitive (sqfPrimitiveSplit p).2 := by
    apply primitive_of_scalarContent_one
    exact sqfPrimitiveSplit_primitive p hzero
  have hone := primitive_const_normalized_eq_one hprimitive hconst
    (sqfPrimitiveSplit_normalized p)
  have hrestore := sqfPrimitiveSplit_product p
  rw [hone, MvPoly.mul_one] at hrestore
  exact hrestore

private theorem product_sqfOps [NatNoZero R] (m : Nat)
    (order : Mono m → Mono m → Ordering) [IsMonomialOrder order]
    (p : MvPoly m R order) :
    C ((sqfOps (R := R) m).decomp order p).content *
        sqfProduct ((sqfOps (R := R) m).decomp order p).factors = p := by
  induction m with
  | zero =>
      simp only [sqfOps, sqfBase]
      rw [sqfProduct_nil, MvPoly.mul_one]
      by_cases hzero : (sqfPrimitiveSplit p).2 = 0
      · exact split_content_of_zero p hzero
      · apply split_content_of_const p hzero
        unfold IsConst
        apply List.eq_nil_iff_forall_not_mem.mpr
        exact fun i _ => Fin.elim0 i
  | succ m ih =>
      simp only [sqfOps, sqfStep]
      split <;> rename_i hterminal
      · rw [sqfProduct_nil, MvPoly.mul_one]
        simp only [Bool.or_eq_true, beq_iff_eq] at hterminal
        rcases hterminal with hzero | hunit
        · exact split_content_of_zero p hzero
        · exact split_content_of_unit p hunit
      · have hq0 : (sqfPrimitiveSplit p).2 ≠ 0 := by
          intro hzero
          rw [hzero] at hterminal
          simp at hterminal
        have hqunit : polyIsUnit (sqfPrimitiveSplit p).2 ≠ true := by
          intro hunit
          rw [hunit] at hterminal
          simp at hterminal
        cases hvars : (sqfPrimitiveSplit p).2.vars with
        | nil =>
            rw [sqfProduct_nil, MvPoly.mul_one]
            exact split_content_of_const p hq0 hvars
        | cons i tail =>
            let q := (sqfPrimitiveSplit p).2
            let coefficientPart := contentIn i Mono.lex q
            let coefficientDecomp :=
              (sqfOps (R := R) m).decomp Mono.lex coefficientPart
            let rawMainPart := primPartIn i Mono.lex q
            let mainSplit := sqfPrimitiveSplit rawMainPart
            let mainPart := mainSplit.2
            let deriv := derivative i mainPart
            let repeated := gcd mainPart deriv
            let b := quotient mainPart repeated
            let c := quotient deriv repeated
            let d := c - derivative i b
            let mainFactors :=
              yunLoop i (mainPart.totalDegree + 1) 1 b d []
            let liftedFactors : List (SqfFactor (m + 1) R order) :=
              coefficientDecomp.factors.map fun factor =>
              { factor := constIn (cmp := order) i Mono.lex factor.factor
                multiplicity := factor.multiplicity }
            have hlower :
                C coefficientDecomp.content *
                    sqfProduct coefficientDecomp.factors = coefficientPart := by
              exact ih Mono.lex coefficientPart
            have hembedded :
                (C coefficientDecomp.content : MvPoly (m + 1) R order) *
                    sqfProduct liftedFactors =
                  constIn i Mono.lex coefficientPart := by
              have h := congrArg
                (constIn (cmp := order) i Mono.lex) hlower
              rw [constIn_mul, constIn_C, ← sqfProduct_map_constIn] at h
              exact h
            have hqRestore :
                constIn i Mono.lex coefficientPart * rawMainPart = q :=
              contentIn_mul_primPartIn i Mono.lex q
            have hraw0 : rawMainPart ≠ 0 := by
              intro hzero
              apply hq0
              change q = 0
              rw [← hqRestore, hzero, MvPoly.mul_zero]
            have hmainRestore :
                (C mainSplit.1 : MvPoly (m + 1) R order) * mainPart =
                  rawMainPart := sqfPrimitiveSplit_product rawMainPart
            have hmain0 : mainPart ≠ 0 := by
              intro hzero
              apply hraw0
              rw [← hmainRestore, hzero, MvPoly.mul_zero]
            have hmainPrimitive : Primitive mainPart := by
              apply primitive_of_scalarContent_one
              exact sqfPrimitiveSplit_primitive rawMainPart hmain0
            have hmainContent : contentIn i Mono.lex mainPart = 1 := by
              have hrawContent : contentIn i Mono.lex rawMainPart = 1 :=
                primPartIn_content i Mono.lex hq0
              apply contentIn_one_of_dvd i hrawContent
              exact ⟨C mainSplit.1, hmainRestore.symm⟩
            have hmainProduct : sqfProduct mainFactors = mainPart := by
              exact yunLoop_product_initial i hmain0 hmainPrimitive
                (sqfPrimitiveSplit_normalized rawMainPart) hmainContent
            have hfactors :
                sqfProduct (liftedFactors.foldl
                  (fun acc factor => mergeSqfFactor factor acc) mainFactors) =
                    sqfProduct liftedFactors * sqfProduct mainFactors :=
              sqfProduct_merge_fold liftedFactors mainFactors
            have hscalar :
                (C ((sqfPrimitiveSplit p).1 *
                    coefficientDecomp.content * mainSplit.1) :
                    MvPoly (m + 1) R order) =
                  C (sqfPrimitiveSplit p).1 *
                    C coefficientDecomp.content * C mainSplit.1 := by
              rw [C_mul_C, C_mul_C]
            have hpRestore := sqfPrimitiveSplit_product p
            change C (sqfPrimitiveSplit p).1 * q = p at hpRestore
            change
              C ((sqfPrimitiveSplit p).1 * coefficientDecomp.content *
                  mainSplit.1) *
                sqfProduct (liftedFactors.foldl
                  (fun acc factor => mergeSqfFactor factor acc) mainFactors) =
                p
            rw [hfactors, hscalar]
            calc
              (C (sqfPrimitiveSplit p).1 * C coefficientDecomp.content *
                    C mainSplit.1) *
                  (sqfProduct liftedFactors * sqfProduct mainFactors) =
                  C (sqfPrimitiveSplit p).1 *
                    (C coefficientDecomp.content * sqfProduct liftedFactors) *
                    (C mainSplit.1 * sqfProduct mainFactors) := by grind
              _ = C (sqfPrimitiveSplit p).1 *
                    constIn i Mono.lex coefficientPart * rawMainPart := by
                rw [hembedded, hmainProduct, hmainRestore]
              _ = C (sqfPrimitiveSplit p).1 * q := by
                rw [MvPoly.mul_assoc, hqRestore]
              _ = p := hpRestore

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
  · rcases hperfect with ⟨prime, hprime, hchar, hroot⟩
    let q := primPart p
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
    · have hprimitive : Primitive q := by
        apply primitive_of_scalarContent_one
        change content q = 1
        exact content_primPart hp
      change polyIsUnit (gcdList (q :: derivatives q)) = true ↔ Squarefree p
      rw [gcdList_unit_iff_squarefree_of_kernel q hprimitive
        (fun hsq g hgq hg0 hderiv =>
          isConst_of_derivatives_zero_perfect hprime hchar hroot
            hsq hgq hg0 hderiv), squarefree_primPart p]

theorem radical_squarefree [IsMonomialOrder cmp] [NatNoZero R]
    (p : MvPoly n R cmp) (hp : p ≠ 0) : Squarefree (radical p) := by
  let q := polyNormalize (primPart p)
  have hrestore : C (sqfPrimitiveSplit p).1 * q = p :=
    sqfPrimitiveSplit_product p
  have hq0 : q ≠ 0 := by
    intro hzero
    apply hp
    rw [← hrestore, hzero, MvPoly.mul_zero]
  let g := gcdList (q :: derivatives q)
  have hgq : g ∣ q := gcdList_dvd (List.mem_cons_self ..)
  have hg0 : g ≠ 0 := by
    intro hzero
    rcases hgq with ⟨a, ha⟩
    rw [hzero, MvPoly.mul_zero] at ha
    exact hq0 ha
  let r := quotient q g
  have hreconstruct : r * g = q := quotient_mul_of_dvd hg0 hgq
  have hr0 : r ≠ 0 := by
    intro hzero
    apply hq0
    rw [← hreconstruct, hzero, MvPoly.zero_mul]
  unfold radical
  simp only [beq_iff_eq]
  change Squarefree
    (if q = 0 then 0 else quotient q (gcdList (q :: derivatives q)))
  rw [ite_eq_right hq0]
  change Squarefree r
  refine ⟨hr0, ?_⟩
  intro d hdd
  have hdr : d ∣ r := by
    rcases hdd with ⟨a, ha⟩
    refine ⟨a * d, ?_⟩
    rw [ha]
    grind
  have hdderiv : ∀ i, d ∣ derivative i r :=
    fun i => derivative_dvd_of_square_dvd i hdd
  apply isConst_of_all_powers_dvd hg0
  exact powers_dvd_derivative_gcd rfl hreconstruct hdr hdderiv

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
  rw [sqfProduct_from]
  exact product_sqfOps n cmp p

/-- Every polynomial returned by square-free decomposition is square-free. -/
theorem sqfDecomp_squarefree [IsMonomialOrder cmp] [NatNoZero R]
    (p : MvPoly n R cmp) :
    ∀ f ∈ (sqfDecomp p).factors, Squarefree f.factor := by
  simpa [sqfDecomp] using
    (properties_sqfOps (R := R) n cmp p).squarefree

theorem sqfDecomp_primitive [IsMonomialOrder cmp] [NatNoZero R]
    (p : MvPoly n R cmp) :
    ∀ f ∈ (sqfDecomp p).factors, content f.factor = 1 := by
  intro factor hfactor
  apply content_eq_one_of_primitive
  exact (properties_sqfOps (R := R) n cmp p).primitive factor hfactor

theorem sqfDecomp_coprime [IsMonomialOrder cmp] [NatNoZero R]
    (p : MvPoly n R cmp) :
    ∀ f ∈ (sqfDecomp p).factors, ∀ g ∈ (sqfDecomp p).factors,
      f.multiplicity ≠ g.multiplicity →
        ∀ d, d ∣ f.factor → d ∣ g.factor → GcdOps.isUnit d = true := by
  intro left hleft right hright hmultiplicity
  have hne : left ≠ right := by
    intro heq
    apply hmultiplicity
    exact congrArg SqfFactor.multiplicity heq
  have hcoprime := coprime_of_mem
    (properties_sqfOps (R := R) n cmp p).pairwise
    left hleft right hright hne
  exact hcoprime

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
  simpa [sqfDecomp] using
    (properties_sqfOps (R := R) n cmp p).nonconstant

end Hex.MvPoly
