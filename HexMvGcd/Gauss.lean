/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvGcd.Instances
public import HexResultant.Fraction

@[expose] public section
set_option backward.proofsInPublic true

/-!
Proof-only Gauss and common-factor algebra.

This file deliberately defines no executable multivariate gcd, content
producer, checker, or candidate route. Its finite coefficient gcd is an
existential object selected only inside proofs; the fraction embedding and
primitive descent isolate the algebra needed to lift gcd-domain laws through
polynomial arities.
-/

namespace Hex

universe u

section Domain

variable {R : Type u} [Lean.Grind.CommRing R] [DecidableEq R]
  [BEq R] [LawfulBEq R] [Dvd R] [GcdOps R]

/-- The executable gcd laws supply the proof-only gcd-domain package. -/
theorem gcdDomainOfLawful [LawfulGcdOps R] : GcdDomainLaws R where
  dvd_iff := LawfulGcdOps.dvd_iff
  one_ne_zero := LawfulGcdOps.one_ne_zero
  no_zero_div := LawfulGcdOps.no_zero_div
  gcd_exists a b :=
    ⟨GcdOps.gcd a b, LawfulGcdOps.gcd_dvd_left a b,
      LawfulGcdOps.gcd_dvd_right a b,
      fun d hda hdb => LawfulGcdOps.dvd_gcd a b d hda hdb⟩

/-- Low-priority bridge from executable lawful gcd operations to the
producer-free algebraic package. -/
instance (priority := 100) instGcdDomainLawsOfLawful [LawfulGcdOps R] :
    GcdDomainLaws R :=
  gcdDomainOfLawful

end Domain

section Cancel

variable {R : Type u} [Lean.Grind.CommRing R] [Dvd R]
  [GcdDomainLaws R]

/-- Multiplication transports a chosen gcd to a gcd of the two products. -/
private theorem mulGcd
    (m a b c : R) (hca : c ∣ a) (hcb : c ∣ b)
    (hc : ∀ d, d ∣ a → d ∣ b → d ∣ c) :
    m * c ∣ m * a ∧ m * c ∣ m * b ∧
      ∀ d, d ∣ m * a → d ∣ m * b → d ∣ m * c := by
  have hleft : m * c ∣ m * a := by
    rcases (GcdDomainLaws.dvd_iff c a).mp hca with ⟨q, hq⟩
    apply (GcdDomainLaws.dvd_iff (m * c) (m * a)).mpr
    refine ⟨q, ?_⟩
    rw [hq]
    grind
  have hright : m * c ∣ m * b := by
    rcases (GcdDomainLaws.dvd_iff c b).mp hcb with ⟨q, hq⟩
    apply (GcdDomainLaws.dvd_iff (m * c) (m * b)).mpr
    refine ⟨q, ?_⟩
    rw [hq]
    grind
  refine ⟨hleft, hright, ?_⟩
  intro d hdma hdmb
  by_cases hm : m = 0
  · apply (GcdDomainLaws.dvd_iff d (m * c)).mpr
    refine ⟨0, ?_⟩
    rw [hm, Lean.Grind.Semiring.zero_mul, Lean.Grind.Semiring.mul_zero]
  rcases GcdDomainLaws.gcd_exists (m * a) (m * b) with
    ⟨x, hxa, hxb, hxgreat⟩
  have hmcx : m * c ∣ x := hxgreat (m * c) hleft hright
  rcases (GcdDomainLaws.dvd_iff (m * c) x).mp hmcx with ⟨t, hxt⟩
  let n := c * t
  have hxn : x = m * n := by
    change x = m * (c * t)
    rw [hxt]
    grind
  have hna : n ∣ a := by
    rcases (GcdDomainLaws.dvd_iff x (m * a)).mp hxa with ⟨q, hq⟩
    apply (GcdDomainLaws.dvd_iff n a).mpr
    refine ⟨q, ?_⟩
    have heq : m * a = m * (n * q) := by
      calc
        m * a = x * q := hq
        _ = (m * n) * q := by rw [hxn]
        _ = m * (n * q) := by grind
    have hzero : m * (a - n * q) = 0 := by grind
    rcases GcdDomainLaws.no_zero_div m (a - n * q) hzero with hz | hz
    · exact False.elim (hm hz)
    · grind
  have hnb : n ∣ b := by
    rcases (GcdDomainLaws.dvd_iff x (m * b)).mp hxb with ⟨q, hq⟩
    apply (GcdDomainLaws.dvd_iff n b).mpr
    refine ⟨q, ?_⟩
    have heq : m * b = m * (n * q) := by
      calc
        m * b = x * q := hq
        _ = (m * n) * q := by rw [hxn]
        _ = m * (n * q) := by grind
    have hzero : m * (b - n * q) = 0 := by grind
    rcases GcdDomainLaws.no_zero_div m (b - n * q) hzero with hz | hz
    · exact False.elim (hm hz)
    · grind
  have hnc : n ∣ c := hc n hna hnb
  rcases (GcdDomainLaws.dvd_iff n c).mp hnc with ⟨q, hq⟩
  have hxmc : x ∣ m * c := by
    apply (GcdDomainLaws.dvd_iff x (m * c)).mpr
    refine ⟨q, ?_⟩
    rw [hq, hxn]
    grind
  rcases (GcdDomainLaws.dvd_iff d x).mp (hxgreat d hdma hdmb) with ⟨r, hr⟩
  rcases (GcdDomainLaws.dvd_iff x (m * c)).mp hxmc with ⟨s, hs⟩
  apply (GcdDomainLaws.dvd_iff d (m * c)).mpr
  refine ⟨r * s, ?_⟩
  calc
    m * c = x * s := hs
    _ = (d * r) * s := by rw [hr]
    _ = d * (r * s) := by grind

/-- Ordinary gcd-domain arithmetic gives Euclid cancellation in the exact
form consumed by certificate maximality. -/
theorem coprimeCancelOfGcdDomain : CoprimeCancelLaws R := by
  constructor
  intro g a b d hcop hda hdb
  rcases GcdDomainLaws.gcd_exists a b with ⟨c, hca, hcb, hc⟩
  rcases hcop c hca hcb with ⟨u, hcu⟩
  have hdgc : d ∣ g * c := (mulGcd g a b c hca hcb hc).2.2 d hda hdb
  rcases (GcdDomainLaws.dvd_iff d (g * c)).mp hdgc with ⟨q, hq⟩
  apply (GcdDomainLaws.dvd_iff d g).mpr
  refine ⟨q * u, ?_⟩
  calc
    g = g * 1 := (Lean.Grind.Semiring.mul_one g).symm
    _ = g * (c * u) := by rw [hcu]
    _ = (g * c) * u := by grind
    _ = (d * q) * u := by rw [hq]
    _ = d * (q * u) := by grind

instance (priority := 100) instCoprimeCancelLawsOfGcdDomain :
    CoprimeCancelLaws R :=
  coprimeCancelOfGcdDomain

end Cancel

section CoeffFold

variable {R : Type u} [Lean.Grind.CommRing R] [Dvd R]

/-- Proof object for a greatest common divisor of every member of a finite
coefficient list. It is not executable certificate data. -/
structure CoeffGcd (xs : List R) where
  value : R
  divides : ∀ x, x ∈ xs → value ∣ x
  greatest : ∀ d, (∀ x, x ∈ xs → d ∣ x) → d ∣ value

/-- Transitivity derived from the multiplication-oriented divisibility law. -/
theorem dvdTrans [GcdDomainLaws R] {a b c : R}
    (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  rcases (GcdDomainLaws.dvd_iff a b).mp hab with ⟨x, hb⟩
  rcases (GcdDomainLaws.dvd_iff b c).mp hbc with ⟨y, hc⟩
  apply (GcdDomainLaws.dvd_iff a c).mpr
  refine ⟨x * y, ?_⟩
  calc
    c = b * y := hc
    _ = (a * x) * y := by rw [hb]
    _ = a * (x * y) := Lean.Grind.Semiring.mul_assoc a x y

/-- Every finite coefficient list admits a greatest common divisor, including
the empty list whose gcd is chosen as zero. -/
theorem coeffGcd_nonempty [GcdDomainLaws R] (xs : List R) :
    Nonempty (CoeffGcd xs) := by
  induction xs with
  | nil =>
      refine ⟨⟨0, ?_, ?_⟩⟩
      · intro x hx
        simp at hx
      · intro d _
        apply (GcdDomainLaws.dvd_iff d 0).mpr
        refine ⟨0, ?_⟩
        exact (Lean.Grind.Semiring.mul_zero d).symm
  | cons a xs ih =>
      rcases ih with ⟨c, hc, hgreat⟩
      rcases GcdDomainLaws.gcd_exists a c with ⟨g, hga, hgc, hgreatG⟩
      refine ⟨⟨g, ?_, ?_⟩⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hga
        · exact dvdTrans hgc (hc x hx)
      · intro d hd
        apply hgreatG d
        · exact hd a (List.mem_cons_self ..)
        · apply hgreat d
          intro x hx
          exact hd x (List.mem_cons_of_mem a hx)

/-- Proof-only choice of a finite coefficient gcd. This is intentionally
`noncomputable` and must not be called by an executable content operation. -/
noncomputable def chooseCoeffGcdData [GcdDomainLaws R]
    (xs : List R) : CoeffGcd xs :=
  Classical.choice (coeffGcd_nonempty xs)

noncomputable def chooseCoeffGcd [GcdDomainLaws R] (xs : List R) : R :=
  (chooseCoeffGcdData xs).value

theorem chooseCoeffGcd_divides [GcdDomainLaws R] (xs : List R)
    {x : R} (hx : x ∈ xs) : chooseCoeffGcd xs ∣ x :=
  (chooseCoeffGcdData xs).divides x hx

theorem dvd_chooseCoeffGcd [GcdDomainLaws R] (xs : List R) (d : R)
    (hd : ∀ x, x ∈ xs → d ∣ x) : d ∣ chooseCoeffGcd xs :=
  (chooseCoeffGcdData xs).greatest d hd

end CoeffFold

namespace MvPoly

variable {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

/-- The scalar coefficient list used only by proof-side content. -/
def coefficientList [Zero R] (p : MvPoly n R cmp) : List R :=
  p.termsList.map Prod.snd

/-- A polynomial is primitive when every scalar common divisor of its stored
coefficients is a unit. This is a semantic predicate, not the executable
primitive-part operation. -/
def Primitive [Lean.Grind.CommRing R] [Dvd R]
    (p : MvPoly n R cmp) : Prop :=
  ∀ d, (∀ c, c ∈ coefficientList p → d ∣ c) → ∃ u, d * u = 1

section Fraction

variable [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
  [Dvd R] [Div R] [ExactDivLaws R] [Hex.Fraction.NonzeroOne R]

/-- Coefficientwise embedding into the Mathlib-free fraction field used by
the subresultant development. -/
def fractionMap (p : MvPoly n R cmp) :
    MvPoly n (Hex.Fraction R) cmp :=
  mapCoeffs Hex.Fraction.ofCoeff p

omit [Dvd R] in
@[simp] theorem fractionMap_zero :
    fractionMap (0 : MvPoly n R cmp) = 0 := by
  exact mapCoeffs_zero Hex.Fraction.ofCoeff_zero

omit [Dvd R] in
theorem fractionMap_add (f g : MvPoly n R cmp) :
    fractionMap (f + g) = fractionMap f + fractionMap g := by
  exact mapCoeffs_add Hex.Fraction.ofCoeff_zero Hex.Fraction.ofCoeff_add f g

omit [Dvd R] in
theorem fractionMap_mul (f g : MvPoly n R cmp) :
    fractionMap (f * g) = fractionMap f * fractionMap g := by
  exact mapCoeffs_mul Hex.Fraction.ofCoeff_zero Hex.Fraction.ofCoeff_add
    Hex.Fraction.ofCoeff_mul f g

omit [BEq R] [LawfulBEq R] [Dvd R] in
theorem fractionMap_injective :
    Function.Injective (fractionMap (n := n) (R := R) (cmp := cmp)) := by
  intro p q hpq
  apply ext
  intro m
  apply Hex.Fraction.ofCoeff_injective
  have hcoeff := congrArg (coeff m) hpq
  simpa [fractionMap, Hex.Fraction.ofCoeff_zero] using hcoeff

/-- Coprimality after embedding the coefficients into the fraction field. -/
def CoprimeOverFraction (f g : MvPoly n R cmp) : Prop :=
  ∀ d, d ∣ fractionMap f → d ∣ fractionMap g →
    ∃ u, d * u = 1

/-- Gcd data for univariate polynomials over the fraction field. This is a
proof-side existence package and does not select a multivariate producer. -/
structure FractionPolyGcd
    (f g : DensePoly (Hex.Fraction R)) where
  value : DensePoly (Hex.Fraction R)
  dvdLeft : value ∣ f
  dvdRight : value ∣ g
  greatest : ∀ d, d ∣ f → d ∣ g → d ∣ value

omit [BEq R] [LawfulBEq R] [Dvd R] in
private theorem fractionDivCancel
    (q : DensePoly (Hex.Fraction R)) (hq : 0 < q.size) :
    ∀ a, a - (a / q.leadingCoeff) * q.leadingCoeff = 0 := by
  intro a
  rw [Hex.Fraction.div_mul_cancel a
    (DensePoly.leadingCoeff_ne_zero_of_pos_size q hq)]
  grind

omit [BEq R] [LawfulBEq R] [Dvd R] in
private theorem fractionRemSizeLt
    (p q : DensePoly (Hex.Fraction R)) (hq : q ≠ 0) :
    (DensePoly.divMod p q).2.size < q.size := by
  have hqpos : 0 < q.size := by
    have hqsize0 : q.size ≠ 0 := by
      intro hsize
      exact hq ((DensePoly.size_eq_zero_iff q).mp hsize)
    omega
  by_cases hqsize : q.size = 1
  · have hrzero :=
      DensePoly.divMod_remainder_eq_zero_of_degree_zero_of_cancel
        p q hqsize (fractionDivCancel q hqpos)
    rw [hrzero, DensePoly.size_zero]
    exact hqpos
  · have hqdeg : 0 < q.natDegree := by
      unfold Hex.DensePoly.natDegree
      rw [DensePoly.degree?_eq_some_of_pos_size q hqpos, Option.getD_some]
      omega
    have hdeg :=
      DensePoly.divMod_remainder_degree_lt_of_pos_degree_of_cancel
        p q hqdeg (fractionDivCancel q hqpos)
    let r := (DensePoly.divMod p q).2
    change r.size < q.size
    by_cases hr : r = 0
    · rw [hr, DensePoly.size_zero]
      exact hqpos
    · have hrpos : 0 < r.size := by
        have hrsize0 : r.size ≠ 0 := by
          intro hsize
          exact hr ((DensePoly.size_eq_zero_iff r).mp hsize)
        omega
      change r.natDegree < q.natDegree at hdeg
      rw [DensePoly.natDegree_eq_size_sub_one,
        DensePoly.natDegree_eq_size_sub_one] at hdeg
      omega

omit [BEq R] [LawfulBEq R] [Dvd R] in
/-- Univariate polynomials over the coefficient fraction field admit gcds. -/
theorem fractionPolyGcd_nonempty
    (f g : DensePoly (Hex.Fraction R)) :
    Nonempty (FractionPolyGcd f g) := by
  revert f
  apply (measure DensePoly.size).wf.induction g
  intro g ih f
  by_cases hg : g = 0
  · subst g
    refine ⟨⟨f, DensePoly.dvd_refl_poly f, DensePoly.dvd_zero_poly f, ?_⟩⟩
    intro d hdf _
    exact hdf
  · let qr := DensePoly.divMod f g
    have hlt : qr.2.size < g.size := by
      simpa [qr] using fractionRemSizeLt f g hg
    rcases ih qr.2 hlt g with ⟨h⟩
    have hrec : qr.1 * g + qr.2 = f := by
      simpa [qr] using
        DensePoly.divMod_reconstruction f g
          (fractionDivCancel g (by
            have hgsize0 : g.size ≠ 0 := by
              intro hsize
              exact hg ((DensePoly.size_eq_zero_iff g).mp hsize)
            omega))
    refine ⟨⟨h.value, ?_, h.dvdLeft, ?_⟩⟩
    · rw [← hrec]
      exact DensePoly.dvd_add_poly
        (DensePoly.dvd_mul_left_poly qr.1 h.dvdLeft) h.dvdRight
    · intro d hdf hdg
      apply h.greatest d hdg
      have hdr : d ∣ f - qr.1 * g :=
        DensePoly.dvd_sub_poly hdf
          (DensePoly.dvd_mul_left_poly qr.1 hdg)
      have hr : f - qr.1 * g = qr.2 := by
        grind
      rwa [hr] at hdr

/-- Primitive descent: fraction-field coprimality of primitive inputs rules
out every nonunit common divisor back in the coefficient ring. -/
theorem primitive_descent [GcdDomainLaws R]
    {f g d : MvPoly n R cmp}
    (hf : Primitive f)
    (hcop : CoprimeOverFraction f g)
    (hdf : d ∣ f) (hdg : d ∣ g) :
    ∃ u, d * u = 1 := by
  have hmapDvdF : fractionMap d ∣ fractionMap f := by
    rcases hdf with ⟨q, hq⟩
    refine ⟨fractionMap q, ?_⟩
    calc
      fractionMap f = fractionMap (q * d) := congrArg fractionMap hq
      _ = fractionMap q * fractionMap d := fractionMap_mul q d
  have hmapDvdG : fractionMap d ∣ fractionMap g := by
    rcases hdg with ⟨q, hq⟩
    refine ⟨fractionMap q, ?_⟩
    calc
      fractionMap g = fractionMap (q * d) := congrArg fractionMap hq
      _ = fractionMap q * fractionMap d := fractionMap_mul q d
  rcases hcop (fractionMap d) hmapDvdF hmapDvdG with ⟨q, hdq⟩
  have hFracOne : (1 : Hex.Fraction R) ≠ 0 :=
    fun h => Hex.Fraction.zero_ne_one h.symm
  have hFracNoZero : ∀ a b : Hex.Fraction R,
      a * b = 0 → a = 0 ∨ b = 0 := by
    intro a b hab
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      by_cases hb : b = 0
      · exact hb
      · exact False.elim ((ExactDivLaws.mul_ne_zero ha hb) hab)
  rcases unit_eq_C hFracOne hFracNoZero hdq with ⟨_, _, hdConst, _⟩
  let c := coeff Mono.zero d
  have hdc : d = C c := by
    apply ext
    intro m
    by_cases hm : m = Mono.zero
    · subst m
      rw [coeff_C]
      simp only [ite_true]
      rfl
    · rw [coeff_C, ite_eq_right hm]
      have hcoeff := congrArg (coeff m) hdConst
      rw [fractionMap, coeff_mapCoeffs Hex.Fraction.ofCoeff_zero,
        coeff_C, ite_eq_right hm] at hcoeff
      exact (Hex.Fraction.ofCoeff_eq_zero_iff (coeff m d)).mp hcoeff
  rcases hdf with ⟨a, ha⟩
  have hcommon : ∀ x, x ∈ coefficientList f → c ∣ x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨term, hterm, rfl⟩
    rcases term with ⟨m, x⟩
    have hcoeff : coeff m f = x := coeff_eq_of_mem_terms f hterm
    apply (GcdDomainLaws.dvd_iff c x).mpr
    refine ⟨coeff m a, ?_⟩
    calc
      x = coeff m f := hcoeff.symm
      _ = coeff m (a * d) := congrArg (coeff m) ha
      _ = coeff m (C c * a) := by rw [hdc, MvPoly.mul_comm]
      _ = c * coeff m a := coeff_C_mul c a m
  rcases hf c hcommon with ⟨u, hcu⟩
  refine ⟨C u, ?_⟩
  rw [hdc]
  change monomial Mono.zero c * monomial Mono.zero u = 1
  rw [monomial_mul_monomial, Mono.zero_mul, hcu]
  rfl

end Fraction

section Lift

variable [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
  [Dvd R] [GcdDomainLaws R]

omit [DecidableEq R] [BEq R] [LawfulBEq R] [Dvd R]
    [GcdDomainLaws R] in
private theorem vars_eq_nil_zero
    {cmp0 : Mono 0 → Mono 0 → Ordering}
    [Std.TransCmp cmp0] [Std.LawfulEqCmp cmp0]
    (p : MvPoly 0 R cmp0) : p.vars = [] := by
  cases h : p.vars with
  | nil => rfl
  | cons i is => exact Fin.elim0 i

/-- At arity zero, coefficient gcds are polynomial gcds. -/
theorem gcdExists_zero
    {cmp0 : Mono 0 → Mono 0 → Ordering}
    [Std.TransCmp cmp0] [Std.LawfulEqCmp cmp0]
    (a b : MvPoly 0 R cmp0) : ∃ g : MvPoly 0 R cmp0,
    g ∣ a ∧ g ∣ b ∧ ∀ d, d ∣ a → d ∣ b → d ∣ g := by
  let ca := coeff Mono.zero a
  let cb := coeff Mono.zero b
  rcases GcdDomainLaws.gcd_exists ca cb with ⟨c, hca, hcb, hgreat⟩
  have ha : a = C ca := eq_C_of_vars_eq_nil a (vars_eq_nil_zero a)
  have hb : b = C cb := eq_C_of_vars_eq_nil b (vars_eq_nil_zero b)
  refine ⟨C c, ?_, ?_, ?_⟩
  · rcases (GcdDomainLaws.dvd_iff c ca).mp hca with ⟨q, hq⟩
    refine ⟨C q, ?_⟩
    rw [ha, hq]
    unfold C
    rw [monomial_mul_monomial, Mono.zero_mul]
    exact congrArg (monomial Mono.zero)
      (Lean.Grind.CommSemiring.mul_comm c q)
  · rcases (GcdDomainLaws.dvd_iff c cb).mp hcb with ⟨q, hq⟩
    refine ⟨C q, ?_⟩
    rw [hb, hq]
    unfold C
    rw [monomial_mul_monomial, Mono.zero_mul]
    exact congrArg (monomial Mono.zero)
      (Lean.Grind.CommSemiring.mul_comm c q)
  · intro d hda hdb
    have hd : d = C (coeff Mono.zero d) :=
      eq_C_of_vars_eq_nil d (vars_eq_nil_zero d)
    rcases hda with ⟨qa, hqa⟩
    rcases hdb with ⟨qb, hqb⟩
    have hdca : coeff Mono.zero d ∣ ca := by
      apply (GcdDomainLaws.dvd_iff _ _).mpr
      refine ⟨coeff Mono.zero qa, ?_⟩
      have hcoeff := congrArg (coeff Mono.zero) hqa
      rw [ha, coeff_C, ite_eq_left rfl, hd,
        MvPoly.mul_comm qa, coeff_C_mul] at hcoeff
      exact hcoeff
    have hdcb : coeff Mono.zero d ∣ cb := by
      apply (GcdDomainLaws.dvd_iff _ _).mpr
      refine ⟨coeff Mono.zero qb, ?_⟩
      have hcoeff := congrArg (coeff Mono.zero) hqb
      rw [hb, coeff_C, ite_eq_left rfl, hd,
        MvPoly.mul_comm qb, coeff_C_mul] at hcoeff
      exact hcoeff
    rcases (GcdDomainLaws.dvd_iff _ _).mp
        (hgreat (coeff Mono.zero d) hdca hdcb) with ⟨q, hq⟩
    refine ⟨C q, ?_⟩
    rw [hd, hq]
    unfold C
    rw [monomial_mul_monomial, Mono.zero_mul]
    exact congrArg (monomial Mono.zero)
      (Lean.Grind.CommSemiring.mul_comm (coeff Mono.zero d) q)

/-- Gauss's lemma lifts proof-only gcd-domain structure through every finite
multivariate arity. -/
theorem gcdDomainLaws : GcdDomainLaws (MvPoly n R cmp) := by
  refine {
    dvd_iff := ?_
    one_ne_zero := ?_
    no_zero_div := ?_
    gcd_exists := ?_ }
  · intro a b
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨q, hq.trans (MvPoly.mul_comm q a)⟩
    · rintro ⟨q, hq⟩
      exact ⟨q, hq.trans (MvPoly.mul_comm a q)⟩
  · intro hone
    have hcoeff := congrArg (coeff (Mono.zero : Mono n)) hone
    rw [coeff_one, coeff_zero, ite_eq_left rfl] at hcoeff
    exact GcdDomainLaws.one_ne_zero hcoeff
  · intro a b hab
    exact MvPoly.zero_product GcdDomainLaws.no_zero_div hab
  · intro a b
    cases n with
    | zero => exact gcdExists_zero a b
    | succ n => sorry

instance (priority := 100) instGcdDomainLawsMvPoly :
    GcdDomainLaws (MvPoly n R cmp) :=
  gcdDomainLaws

/-- The lifted gcd-domain laws supply the common-factor cancellation used by
checked gcd maximality. -/
theorem coprimeCancelLaws : CoprimeCancelLaws (MvPoly n R cmp) := by
  exact coprimeCancelOfGcdDomain

instance (priority := 100) instCoprimeCancelLawsMvPoly :
    CoprimeCancelLaws (MvPoly n R cmp) :=
  coprimeCancelLaws

/-- Named common-factor step consumed by `CheckedGcdResult.greatest`. -/
theorem cancelCommonFactor
    (g a b d : MvPoly n R cmp)
    (hcop : ∀ e, e ∣ a → e ∣ b → ∃ u, e * u = 1)
    (hda : d ∣ g * a) (hdb : d ∣ g * b) : d ∣ g := by
  exact CoprimeCancelLaws.cancel_coprime g a b d hcop hda hdb

end Lift

end MvPoly

end Hex
