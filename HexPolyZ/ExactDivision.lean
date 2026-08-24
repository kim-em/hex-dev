/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyZ.IntegerPolynomial

public section
set_option backward.proofsInPublic true

/-!
Checked exact division for integer dense polynomials.

This is the shared primitive used by integer-polynomial gcd and by
Berlekamp--Zassenhaus recombination.  The latter adds its own policy about
rejecting unit candidates; exact division itself accepts every nonzero exact
divisor, including units.
-/

namespace Hex.ZPoly

namespace DivExact

/-- The first cheap obstruction found before integer-polynomial long division.

The constructors are ordered by the cost of the corresponding check. -/
inductive Reject where
  /-- Division by the zero polynomial is undefined. -/
  | zeroDivisor
  /-- A nonzero divisor cannot have larger degree than a nonzero dividend. -/
  | degree
  /-- The divisor's leading coefficient must divide the dividend's. -/
  | leadingCoeff
  /-- The divisor's coefficient content must divide the dividend's. -/
  | content
  /-- Divisibility must survive evaluation at the fixed small point. -/
  | evaluation
  deriving BEq, DecidableEq, Repr

/-- The fixed small evaluation point used by the final exact-division precheck.

Evaluation at one avoids coefficient growth while still testing a condition
independent of the degree, leading-coefficient, and content checks. -/
@[expose]
def evalPoint : Int := 1

/-- Executable coefficient content used by exact-division rejection. -/
@[expose]
def contentValue (f : ZPoly) : Int :=
  Int.ofNat (DensePoly.contentNatImpl f)

/-- The executable content value agrees with the public specification. -/
theorem contentValue_eq (f : ZPoly) : contentValue f = content f := by
  unfold contentValue content DensePoly.content
  rw [DensePoly.contentNat_eq_contentNatImpl]

/-- Executable Horner evaluation at the fixed rejection point. -/
@[expose]
def evalValue (f : ZPoly) : Int :=
  DensePoly.evalImpl f evalPoint

/-- The executable evaluation value agrees with public polynomial evaluation. -/
theorem evalValue_eq (f : ZPoly) : evalValue f = DensePoly.eval f evalPoint :=
  (DensePoly.eval_eq_evalImpl f evalPoint).symm

/-- Return the first cheap reason that `g` cannot divide `f`, or `none` when
dense exact division is still necessary.

The zero dividend is deliberately allowed past the degree check: every nonzero
polynomial divides zero, with exact quotient zero. -/
@[expose]
def reject? (f g : ZPoly) : Option Reject :=
  if g.isZero then
    some .zeroDivisor
  else if f.isZero then
    none
  else if f.size < g.size then
    some .degree
  else if f.leadingCoeff % g.leadingCoeff != 0 then
    some .leadingCoeff
  else if contentValue f % contentValue g != 0 then
    some .content
  else if evalValue f % evalValue g != 0 then
    some .evaluation
  else
    none

/-- Every exact multiple passes all cheap rejection tests. -/
theorem reject?_eq_none_of_mul (q g : ZPoly) (hg : g ≠ 0) :
    reject? (q * g) g = none := by
  have hgpos : 0 < g.size := size_pos_of_ne_zero g hg
  have hgzero : g.isZero = false :=
    (DensePoly.isZero_eq_false_iff g).2 hgpos
  by_cases hq : q = 0
  · subst q
    rw [DensePoly.zero_mul]
    have hz : (0 : ZPoly).isZero = true := by rfl
    simp [reject?, hgzero, hz]
  · have hqpos : 0 < q.size := size_pos_of_ne_zero q hq
    have hsize := mul_size_eq_top_succ_of_nonzero q g hqpos hgpos
    have hprodpos : 0 < (q * g).size := by omega
    have hprodzero : (q * g).isZero = false :=
      (DensePoly.isZero_eq_false_iff (q * g)).2 hprodpos
    have hnotDegree : ¬ (q * g).size < g.size := by omega
    simp [reject?, hgzero, hprodzero, hnotDegree,
      leadingCoeff_mul_of_nonzero q g hq hg, contentValue_eq, content_mul,
      evalValue_eq, DensePoly.eval_mul_commring]

end DivExact

/-- The exact quotient `f / g`, or `none` when `g = 0` or the executable
integer-polynomial division does not reconstruct `f` exactly. -/
@[expose]
def divExact? (f g : ZPoly) : Option ZPoly :=
  match DivExact.reject? f g with
  | some _ => none
  | none =>
    let qr := DensePoly.divMod f g
    if qr.2 = 0 && qr.1 * g == f then
      some qr.1
    else
      none

/-- Division by the zero polynomial is always rejected. -/
@[simp] theorem divExact?_zero_right (f : ZPoly) : divExact? f 0 = none := by
  have hz : (0 : ZPoly).isZero = true := by rfl
  unfold divExact? DivExact.reject?
  rw [hz]
  simp

/-- A prefilter rejection returns before the dense-division branch. -/
theorem divExact?_eq_none_of_reject {f g : ZPoly} {reason : DivExact.Reject}
    (h : DivExact.reject? f g = some reason) : divExact? f g = none := by
  simp [divExact?, h]

/-- A successful exact division carries the checked multiplication witness. -/
theorem divExact?_product
    {f g q : ZPoly} (h : divExact? f g = some q) : q * g = f := by
  unfold divExact? at h
  split at h
  · contradiction
  · generalize hqr : DensePoly.divMod f g = qr at h
    cases qr with
    | mk quotient remainder =>
        simp only at h
        split at h
        · rename_i hcheck
          cases h
          exact (by
            simpa [Bool.and_eq_true, beq_iff_eq] using hcheck :
              remainder = 0 ∧ q * g = f).2
        · contradiction

/-- Long division returns the witnessed quotient for every exact multiple by
a nonzero integer polynomial. -/
theorem divMod_eq_mul_of_ne_zero
    (f g q : ZPoly) (hg : g ≠ 0) (hmul : q * g = f) :
    DensePoly.divMod f g = (q, 0) := by
  have hgpos : 0 < g.size := by
    rcases Nat.lt_or_ge 0 g.size with hpos | hzero
    · exact hpos
    · exfalso
      apply hg
      exact (DensePoly.size_eq_zero_iff g).mp (Nat.eq_zero_of_le_zero hzero)
  have hlc_ne : g.leadingCoeff ≠ 0 :=
    DensePoly.leadingCoeff_ne_zero_of_pos_size g hgpos
  apply DensePoly.divMod_eq_of_polynomial_mul f g q hg
  · intro a
    exact Int.mul_ediv_cancel a hlc_ne
  · intro a ha
    exact Int.mul_ne_zero ha hlc_ne
  · exact hmul

/-- Exact division succeeds exactly on a supplied multiplication witness when
the divisor is nonzero. -/
theorem divExact?_eq {f g q : ZPoly} (hg : g ≠ 0) :
    divExact? f g = some q ↔ f = q * g := by
  constructor
  · intro h
    exact (divExact?_product h).symm
  · intro hmul
    have hdiv : DensePoly.divMod f g = (q, 0) :=
      divMod_eq_mul_of_ne_zero f g q hg hmul.symm
    have hrejection : DivExact.reject? f g = none := by
      rw [hmul]
      exact DivExact.reject?_eq_none_of_mul q g hg
    unfold divExact?
    rw [hrejection, hdiv]
    simp [hmul]

/-- Every nonzero divisor is found by the executable exact-division check. -/
theorem divExact?_isSome_of_dvd {f g : ZPoly} (hg : g ≠ 0) :
    g ∣ f → (divExact? f g).isSome := by
  rintro ⟨q, hq⟩
  have hmul : f = q * g := by
    rw [DensePoly.mul_comm_poly]
    exact hq
  have hsome : divExact? f g = some q := (divExact?_eq hg).2 hmul
  rw [hsome]
  rfl

/-! Kernel regressions cover every rejection gate, exact and inexact fallthrough,
unit and negative-unit division, and the zero cases. -/

private def degreeDividend : ZPoly := DensePoly.ofList [1, 1]
private def degreeDivisor : ZPoly := DensePoly.ofList [1, 0, 1]
private def leadingDividend : ZPoly := DensePoly.ofList [1, 0, 3]
private def leadingDivisor : ZPoly := DensePoly.ofList [1, 2]
private def contentDividend : ZPoly := DensePoly.ofList [1, 0, 2]
private def contentDivisor : ZPoly := DensePoly.ofList [2, 2]
private def evaluationDividend : ZPoly := DensePoly.ofList [1, 1, 1]
private def evaluationDivisor : ZPoly := DensePoly.ofList [1, 1]

example : DivExact.reject? degreeDividend 0 = some .zeroDivisor := by decide
example : DivExact.reject? degreeDividend degreeDivisor = some .degree := by decide
example : DivExact.reject? leadingDividend leadingDivisor = some .leadingCoeff := by decide
example : DivExact.reject? contentDividend contentDivisor = some .content := by decide
example : DivExact.reject? evaluationDividend evaluationDivisor = some .evaluation := by decide

example : divExact? degreeDividend degreeDivisor = none := by decide
example : divExact? leadingDividend leadingDivisor = none := by decide
example : divExact? contentDividend contentDivisor = none := by decide
example : divExact? evaluationDividend evaluationDivisor = none := by decide

/- `x^2 + 1` passes every cheap test for `x + 1` at evaluation point one,
but the dense exact-division check still rejects it. -/
example : DivExact.reject? (DensePoly.ofList [1, 0, 1]) evaluationDivisor = none := by decide
example : divExact? (DensePoly.ofList [1, 0, 1]) evaluationDivisor = none := by decide

example :
    divExact? (DensePoly.ofList [2, 4, 2]) (DensePoly.ofList [1, 1]) =
      some (DensePoly.ofList [2, 2]) := by
  decide

example :
    divExact? (DensePoly.ofList [2, 4, 2]) (DensePoly.ofList [1, 2]) = none := by
  decide

example (f : ZPoly) : divExact? f 1 = some f := by
  exact (divExact?_eq (by decide)).2 (by rw [DensePoly.mul_one_right_poly])

example :
    divExact? (DensePoly.ofList [2, -4]) (DensePoly.C (-1)) =
      some (DensePoly.ofList [-2, 4]) := by
  decide

example (f : ZPoly) : divExact? f 0 = none := divExact?_zero_right f

example (g : ZPoly) (hg : g ≠ 0) : divExact? 0 g = some 0 := by
  exact (divExact?_eq hg).2 (DensePoly.zero_mul g).symm

end Hex.ZPoly
