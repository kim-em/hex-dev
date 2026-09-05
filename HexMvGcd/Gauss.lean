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

/-- Ordinary gcd-domain arithmetic gives Euclid cancellation in the exact
form consumed by certificate maximality. -/
theorem coprimeCancelOfGcdDomain : CoprimeCancelLaws R := by
  sorry

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

universe v

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
  · have hqdeg : 0 < q.degree?.getD 0 := by
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
      change r.degree?.getD 0 < q.degree?.getD 0 at hdeg
      rw [DensePoly.degree?_eq_some_of_pos_size r hrpos,
        DensePoly.degree?_eq_some_of_pos_size q hqpos,
        Option.getD_some, Option.getD_some] at hdeg
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
    (hf : Primitive f) (hg : Primitive g)
    (hcop : CoprimeOverFraction f g)
    (hdf : d ∣ f) (hdg : d ∣ g) :
    ∃ u, d * u = 1 := by
  sorry

end Fraction

section Lift

variable [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
  [Dvd R] [GcdDomainLaws R]

/-- Gauss's lemma lifts proof-only gcd-domain structure through every finite
multivariate arity. -/
theorem gcdDomainLaws : GcdDomainLaws (MvPoly n R cmp) := by
  sorry

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
