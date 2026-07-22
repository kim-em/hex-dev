/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexHensel.Basic
public import HexHensel.WordTransport
public import HexPoly.Euclid.MonicUnique

public section

/-!
Executable quadratic Hensel lifting.

This module implements the doubling step that lifts a factorization and its
Bezout witnesses from congruence modulo `m` to congruence modulo `m * m`,
together with the initial theorem surface describing the updated invariants.
-/
namespace Hex

/-- Output of one quadratic Hensel doubling step. The four fields package the
updated leading factor `g` (monic, the input `g` corrected modulo `m^2`), the
updated complementary factor `h`, and the updated Bezout witnesses `s`, `t`
satisfying `s * g + t * h ≡ 1 (mod m^2)`. -/
structure QuadraticLiftResult where
  g : ZPoly
  h : ZPoly
  s : ZPoly
  t : ZPoly

namespace QuadraticLiftResult

/-- Canonical coefficient reduction modulo `m^2`. -/
def reduceModSquare (f : ZPoly) (m : Nat) : ZPoly :=
  ZPoly.reduceModPow f m 2

/-- Residue `f - g * h` corrected by the factor update of the quadratic Hensel
step: starting from `g * h ≡ f (mod m)`, this quantity is divisible by `m` and
its lift drives the first-order correction that achieves `g' * h' ≡ f (mod
m^2)`. -/
def factorError (f g h : ZPoly) : ZPoly :=
  f - g * h

end QuadraticLiftResult

namespace ZPoly

/-- The working modulus `m * m = m²` of one quadratic Hensel doubling step. -/
private def quadraticModulus (m : Nat) : Nat :=
  m * m

/-- Canonical nonnegative residue of `z` in the range `[0, modulus)`. -/
private def canonicalMod (z : Int) (modulus : Nat) : Int :=
  Int.ofNat <| Int.toNat (z % Int.ofNat modulus)

/-- Reduce a single coefficient to its canonical residue modulo `m²`. -/
private def reduceCoeffModSquare (z : Int) (m : Nat) : Int :=
  canonicalMod z (quadraticModulus m)

/-- Polynomial sum `f + g` with every coefficient reduced modulo `m²`. -/
private def addModSquare (f g : ZPoly) (m : Nat) : ZPoly :=
  QuadraticLiftResult.reduceModSquare (f + g) m

/-- Polynomial difference `f - g` with every coefficient reduced modulo `m²`. -/
private def subModSquare (f g : ZPoly) (m : Nat) : ZPoly :=
  QuadraticLiftResult.reduceModSquare (f - g) m

/-- Polynomial product `f * g` with every coefficient reduced modulo `m²`. -/
private def mulModSquare (f g : ZPoly) (m : Nat) : ZPoly :=
  QuadraticLiftResult.reduceModSquare (f * g) m

/-- Fuel-driven long-division kernel returning the quotient/remainder of the
running `rem` by the monic divisor `q`, with all arithmetic reduced modulo `m²`.
The Hensel theorem surface supplies monic divisors, so this exploits that
invariant to avoid coefficient division in the modular hot path. -/
private def divModMonicModSquareAux
    (m : Nat) (q : ZPoly) : Nat → ZPoly → ZPoly → ZPoly × ZPoly
  | 0, quot, rem => (quot, rem)
  | fuel + 1, quot, rem =>
      if q.isZero then
        (0, QuadraticLiftResult.reduceModSquare rem m)
      else
        match rem.degree?, q.degree? with
        | some rd, some qd =>
            if rd < qd then
              (quot, rem)
            else
              let k := rd - qd
              let coeff := reduceCoeffModSquare rem.leadingCoeff m
              let term := DensePoly.monomial k coeff
              let quot := addModSquare quot term m
              let rem := subModSquare rem (mulModSquare term q m) m
              divModMonicModSquareAux m q fuel quot rem
        | _, _ => (quot, rem)

/-- Quotient and remainder of `p` divided by the monic divisor `q`, working
modulo `m²`, with the dividend size supplying the recursion fuel. -/
private def divModMonicModSquare (p q : ZPoly) (m : Nat) : ZPoly × ZPoly :=
  let p := QuadraticLiftResult.reduceModSquare p m
  divModMonicModSquareAux m q p.size 0 p

/-- `reduceModSquare f m` is congruent to `f` modulo `m²`. -/
private theorem reduceModSquare_congr
    (m : Nat) (f : ZPoly) (hm : 0 < m) :
    ZPoly.congr (QuadraticLiftResult.reduceModSquare f m) f (m * m) := by
  unfold QuadraticLiftResult.reduceModSquare
  have hpow : 0 < m ^ 2 := Nat.pow_pos hm
  simpa [Nat.pow_two] using ZPoly.congr_reduceModPow f m 2 hpow

/-- `addModSquare f g m` is congruent to `f + g` modulo `m²`. -/
private theorem addModSquare_congr
    (m : Nat) (f g : ZPoly) (hm : 0 < m) :
    ZPoly.congr (addModSquare f g m) (f + g) (m * m) := by
  unfold addModSquare
  exact reduceModSquare_congr m (f + g) hm

/-- `subModSquare f g m` is congruent to `f - g` modulo `m²`. -/
private theorem subModSquare_congr
    (m : Nat) (f g : ZPoly) (hm : 0 < m) :
    ZPoly.congr (subModSquare f g m) (f - g) (m * m) := by
  unfold subModSquare
  exact reduceModSquare_congr m (f - g) hm

/-- `mulModSquare f g m` is congruent to `f * g` modulo `m²`. -/
private theorem mulModSquare_congr
    (m : Nat) (f g : ZPoly) (hm : 0 < m) :
    ZPoly.congr (mulModSquare f g m) (f * g) (m * m) := by
  unfold mulModSquare
  exact reduceModSquare_congr m (f * g) hm

/-- Congruence modulo `m` is preserved by subtraction:
`f ≡ f'` and `g ≡ g'` give `f - g ≡ f' - g'`. -/
private theorem congr_sub
    (f g f' g' : ZPoly) (m : Nat)
    (hf : ZPoly.congr f f' m) (hg : ZPoly.congr g g' m) :
    ZPoly.congr (f - g) (f' - g') m := by
  intro i
  rw [DensePoly.coeff_sub f g i]
  · rw [DensePoly.coeff_sub f' g' i]
    · have hfi : (f.coeff i - f'.coeff i) % (m : Int) = 0 := hf i
      have hgi : (g.coeff i - g'.coeff i) % (m : Int) = 0 := hg i
      have hdvd_f : (m : Int) ∣ f.coeff i - f'.coeff i :=
        Int.dvd_of_emod_eq_zero hfi
      have hdvd_g : (m : Int) ∣ g.coeff i - g'.coeff i :=
        Int.dvd_of_emod_eq_zero hgi
      have hcoeff :
          (f.coeff i - g.coeff i) - (f'.coeff i - g'.coeff i) =
            (f.coeff i - f'.coeff i) - (g.coeff i - g'.coeff i) := by
        omega
      rw [hcoeff]
      exact Int.emod_eq_zero_of_dvd (Int.dvd_sub hdvd_f hdvd_g)
    · rfl
  · rfl

/-- Congruence modulo `m` is preserved by left-multiplication by a fixed `b`:
`x ≡ y` gives `b * x ≡ b * y`. -/
private theorem congr_mul_left
    (b x y : ZPoly) (m : Nat)
    (hxy : ZPoly.congr x y m) :
    ZPoly.congr (b * x) (b * y) m :=
  ZPoly.congr_mul b x b y m (ZPoly.congr_refl b m) hxy

/-- Congruence modulo `m²` implies congruence modulo `m`, since `m ∣ m²`. -/
private theorem congr_of_square_mod
    (m : Nat) (f g : ZPoly)
    (hfg : ZPoly.congr f g (m * m)) :
    ZPoly.congr f g m := by
  intro i
  by_cases hm : m = 0
  · subst m
    simpa using hfg i
  · have hdiv : (m : Int) ∣ ((m * m : Nat) : Int) := by
      refine ⟨(m : Int), ?_⟩
      rw [Int.natCast_mul]
    have hsqi : (f.coeff i - g.coeff i) % (((m * m : Nat) : Int)) = 0 := hfg i
    exact Int.emod_eq_zero_of_dvd
      (Int.dvd_trans hdiv (Int.dvd_of_emod_eq_zero hsqi))

/-- `f - f = 0` as a `ZPoly`. -/
private theorem sub_self_eq_zero (f : ZPoly) :
    f - f = 0 := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_sub, DensePoly.coeff_zero]
  · omega
  · rfl

/-- If `g ≡ 0 (mod m)` then `m` divides each coefficient product
`f.coeff i * g.coeff j`. -/
private theorem coeff_product_right_dvd
    (m : Nat) (f g : ZPoly)
    (hg : ZPoly.congr g 0 m) (i j : Nat) :
    (m : Int) ∣ f.coeff i * g.coeff j := by
  have hj_mod : (g.coeff j) % (m : Int) = 0 := by
    simpa using hg j
  rcases Int.dvd_of_emod_eq_zero hj_mod with ⟨a, ha⟩
  refine ⟨f.coeff i * a, ?_⟩
  calc
    f.coeff i * g.coeff j = f.coeff i * ((m : Int) * a) := by rw [ha]
    _ = (m : Int) * (f.coeff i * a) := by grind

/-- One convolution step `mulCoeffStep` keeps the accumulator divisible by `m`
when `g ≡ 0 (mod m)` and the incoming accumulator is divisible by `m`. -/
private theorem mulCoeffStep_right_dvd
    (m : Nat) (f g : ZPoly)
    (hg : ZPoly.congr g 0 m) (n i : Nat) (acc : Int) (j : Nat)
    (hacc : (m : Int) ∣ acc) :
    (m : Int) ∣ DensePoly.mulCoeffStep f g n i acc j := by
  by_cases hij : i + j = n
  · rcases hacc with ⟨a, ha⟩
    rcases coeff_product_right_dvd m f g hg i j with ⟨c, hc⟩
    refine ⟨a + c, ?_⟩
    calc
      DensePoly.mulCoeffStep f g n i acc j
          = acc + f.coeff i * g.coeff j := by simp [DensePoly.mulCoeffStep, hij]
      _ = (m : Int) * a + (m : Int) * c := by rw [ha, hc]
      _ = (m : Int) * (a + c) := by grind
  · simpa [DensePoly.mulCoeffStep, hij] using hacc

/-- Folding the inner convolution steps over `xs` keeps the accumulator
divisible by `m` when `g ≡ 0 (mod m)` and the initial accumulator is. -/
private theorem foldl_mulCoeffStep_right_dvd
    (m : Nat) (f g : ZPoly)
    (hg : ZPoly.congr g 0 m) (n i : Nat) (xs : List Nat) (acc : Int)
    (hacc : (m : Int) ∣ acc) :
    (m : Int) ∣ xs.foldl (DensePoly.mulCoeffStep f g n i) acc := by
  induction xs generalizing acc with
  | nil =>
      simpa using hacc
  | cons j xs ih =>
      simpa using
        ih (DensePoly.mulCoeffStep f g n i acc j)
          (mulCoeffStep_right_dvd m f g hg n i acc j hacc)

/-- Folding the full coefficient-sum (outer range over `xs`, inner over
`g.size`) keeps the accumulator divisible by `m` when `g ≡ 0 (mod m)`. -/
private theorem foldl_mulCoeffSum_right_dvd
    (m : Nat) (f g : ZPoly)
    (hg : ZPoly.congr g 0 m) (n : Nat) (xs : List Nat) (acc : Int)
    (hacc : (m : Int) ∣ acc) :
    (m : Int) ∣
      xs.foldl
        (fun acc i => (List.range g.size).foldl (DensePoly.mulCoeffStep f g n i) acc)
        acc := by
  induction xs generalizing acc with
  | nil =>
      simpa using hacc
  | cons i xs ih =>
      have hinner :
          (m : Int) ∣
            (List.range g.size).foldl (DensePoly.mulCoeffStep f g n i) acc :=
        foldl_mulCoeffStep_right_dvd m f g hg n i (List.range g.size) acc hacc
      simpa using ih
        ((List.range g.size).foldl (DensePoly.mulCoeffStep f g n i) acc) hinner

/-- If `g ≡ 0 (mod m)` then `f * g ≡ 0 (mod m)` for any `f`. -/
private theorem mul_right_zero_mod_base
    (m : Nat) (f g : ZPoly)
    (hg : ZPoly.congr g 0 m) :
    ZPoly.congr (f * g) 0 m := by
  intro n
  have hdvd : (m : Int) ∣ (f * g).coeff n := by
    rw [DensePoly.coeff_mul, DensePoly.mulCoeffSum]
    exact foldl_mulCoeffSum_right_dvd m f g hg n (List.range f.size) 0 ⟨0, by simp⟩
  rw [DensePoly.coeff_zero]
  simpa using Int.emod_eq_zero_of_dvd hdvd

/-- One long-division step preserves the reconstruction `quot * q + rem` modulo
`m²`: the updated quotient/remainder pair recombines to the same value. -/
private theorem divModMonicModSquare_step_reconstruct_congr
    (m : Nat) (quot rem term q : ZPoly) (hm : 0 < m) :
    ZPoly.congr
      (addModSquare quot term m * q + subModSquare rem (mulModSquare term q m) m)
      (quot * q + rem)
      (m * m) := by
  have hquot :
      ZPoly.congr (addModSquare quot term m) (quot + term) (m * m) :=
    addModSquare_congr m quot term hm
  have hrem :
      ZPoly.congr
        (subModSquare rem (mulModSquare term q m) m)
        (rem - mulModSquare term q m)
        (m * m) :=
    subModSquare_congr m rem (mulModSquare term q m) hm
  have hmulMod : ZPoly.congr (mulModSquare term q m) (term * q) (m * m) :=
    mulModSquare_congr m term q hm
  have hrem' :
      ZPoly.congr
        (rem - mulModSquare term q m)
        (rem - term * q)
        (m * m) := by
    intro i
    rw [DensePoly.coeff_sub, DensePoly.coeff_sub]
    · have hcoeff :
          rem.coeff i - (mulModSquare term q m).coeff i -
              (rem.coeff i - (term * q).coeff i) =
            -((mulModSquare term q m).coeff i - (term * q).coeff i) := by
        omega
      rw [hcoeff]
      exact Int.emod_eq_zero_of_dvd
        (Int.dvd_neg.mpr (Int.dvd_of_emod_eq_zero (hmulMod i)))
    · show (0 : Int) - (0 : Int) = 0
      omega
    · show (0 : Int) - (0 : Int) = 0
      omega
  have hleft :
      ZPoly.congr
        (addModSquare quot term m * q + subModSquare rem (mulModSquare term q m) m)
        ((quot + term) * q + (rem - term * q))
        (m * m) :=
    ZPoly.congr_add _ _ _ _ (m * m)
      (ZPoly.congr_mul _ _ _ _ (m * m) hquot (ZPoly.congr_refl q (m * m)))
      (ZPoly.congr_trans _ _ _ (m * m) hrem hrem')
  have hright :
      ZPoly.congr ((quot + term) * q + (rem - term * q)) (quot * q + rem) (m * m) := by
    rw [DensePoly.add_mul_sub_cancel_right]
    exact ZPoly.congr_refl (quot * q + rem) (m * m)
  exact ZPoly.congr_trans _ _ _ (m * m) hleft hright

/-- Loop invariant of the division kernel for nonzero divisor `q`: the kernel's
output satisfies `qOut * q + rOut ≡ quot * q + rem (mod m²)`. -/
private theorem divModMonicModSquareAux_reconstruct_congr_of_not_zero
    (m : Nat) (q : ZPoly) (fuel : Nat) (quot rem qOut rOut : ZPoly)
    (hm : 0 < m) (hq : q.isZero = false)
    (hqr : (qOut, rOut) = divModMonicModSquareAux m q fuel quot rem) :
    ZPoly.congr (qOut * q + rOut) (quot * q + rem) (m * m) := by
  induction fuel generalizing quot rem qOut rOut with
  | zero =>
      simp [divModMonicModSquareAux] at hqr
      have hqOut : qOut = quot := hqr.1
      have hrOut : rOut = rem := hqr.2
      subst qOut
      subst rOut
      exact ZPoly.congr_refl (quot * q + rem) (m * m)
  | succ fuel ih =>
      cases hrem : rem.degree? with
      | none =>
          simp [divModMonicModSquareAux, hq, hrem] at hqr
          have hqOut : qOut = quot := hqr.1
          have hrOut : rOut = rem := hqr.2
          subst qOut
          subst rOut
          exact ZPoly.congr_refl (quot * q + rem) (m * m)
      | some rd =>
          cases hqdeg : q.degree? with
          | none =>
              simp [divModMonicModSquareAux, hq, hrem, hqdeg] at hqr
              have hqOut : qOut = quot := hqr.1
              have hrOut : rOut = rem := hqr.2
              subst qOut
              subst rOut
              exact ZPoly.congr_refl (quot * q + rem) (m * m)
          | some qd =>
              by_cases hlt : rd < qd
              · simp [divModMonicModSquareAux, hq, hrem, hqdeg, hlt] at hqr
                have hqOut : qOut = quot := hqr.1
                have hrOut : rOut = rem := hqr.2
                subst qOut
                subst rOut
                exact ZPoly.congr_refl (quot * q + rem) (m * m)
              · simp [divModMonicModSquareAux, hq, hrem, hqdeg, hlt] at hqr
                let k := rd - qd
                let coeff := reduceCoeffModSquare rem.leadingCoeff m
                let term := DensePoly.monomial k coeff
                have hrec :
                    ZPoly.congr (qOut * q + rOut)
                      (addModSquare quot term m * q +
                        subModSquare rem (mulModSquare term q m) m)
                      (m * m) :=
                  ih (addModSquare quot term m)
                    (subModSquare rem (mulModSquare term q m) m)
                    qOut rOut hqr
                have hstep :
                    ZPoly.congr
                      (addModSquare quot term m * q +
                        subModSquare rem (mulModSquare term q m) m)
                      (quot * q + rem)
                      (m * m) :=
                  divModMonicModSquare_step_reconstruct_congr m quot rem term q hm
                exact ZPoly.congr_trans _ _ _ (m * m) hrec hstep

/-- The division result reconstructs the dividend modulo `m²`:
`qOut * q + rOut ≡ p (mod m²)`. -/
private theorem divModMonicModSquare_reconstruct_congr
    (m : Nat) (p q qOut rOut : ZPoly) (hm : 0 < m)
    (hqr : (qOut, rOut) = divModMonicModSquare p q m) :
    ZPoly.congr (qOut * q + rOut) p (m * m) := by
  unfold divModMonicModSquare at hqr
  let pRed := QuadraticLiftResult.reduceModSquare p m
  change (qOut, rOut) = divModMonicModSquareAux m q pRed.size 0 pRed at hqr
  have hpRed : ZPoly.congr pRed p (m * m) :=
    reduceModSquare_congr m p hm
  cases hq : q.isZero with
  | false =>
    have haux :
        ZPoly.congr (qOut * q + rOut) ((0 : ZPoly) * q + pRed) (m * m) :=
      divModMonicModSquareAux_reconstruct_congr_of_not_zero
        m q pRed.size 0 pRed qOut rOut hm hq hqr
    have hzero :
        ((0 : ZPoly) * q + pRed) = pRed := by
      rw [DensePoly.zero_mul, DensePoly.zero_add]
    exact ZPoly.congr_trans _ _ _ (m * m) haux
      (by
        rw [hzero]
        exact hpRed)
  | true =>
    cases hsize : pRed.size with
    | zero =>
        simp [divModMonicModSquareAux, hsize] at hqr
        have hqOut : qOut = 0 := hqr.1
        have hrOut : rOut = pRed := hqr.2
        subst qOut
        subst rOut
        rw [DensePoly.zero_mul, DensePoly.zero_add]
        exact hpRed
    | succ fuel =>
        simp [divModMonicModSquareAux, hq, hsize] at hqr
        have hqOut : qOut = 0 := hqr.1
        have hrOut : rOut = QuadraticLiftResult.reduceModSquare pRed m := hqr.2
        subst qOut
        subst rOut
        rw [DensePoly.zero_mul, DensePoly.zero_add]
        exact ZPoly.congr_trans _ _ _ (m * m)
          (reduceModSquare_congr m pRed hm) hpRed

/-- `coeff_last_eq_leadingCoeff` identifies the last coefficient of a nonempty polynomial with its leading coefficient. -/
private theorem coeff_last_eq_leadingCoeff (f : ZPoly) (hpos : 0 < f.size) :
    f.coeff (f.size - 1) = f.leadingCoeff := by
  cases f with
  | mk coeffs normalized =>
      have hcoeffs : 0 < coeffs.size := by simpa [DensePoly.size] using hpos
      have hidx : coeffs.size - 1 < coeffs.size := Nat.sub_one_lt (Nat.ne_of_gt hcoeffs)
      simp [DensePoly.leadingCoeff, DensePoly.coeff, DensePoly.size]

/-- `monic_of_coeff_eq_one_and_high_coeff_zero` builds monicity from a coefficient equal to one with all higher coefficients zero. -/
private theorem monic_of_coeff_eq_one_and_high_coeff_zero
    (f : ZPoly) (n : Nat)
    (hone : f.coeff n = 1)
    (hhigh : ∀ i, n < i → f.coeff i = 0) :
    DensePoly.Monic f := by
  have hn_lt_size : n < f.size := by
    by_cases hn : n < f.size
    · exact hn
    · have hcoeff := DensePoly.coeff_eq_zero_of_size_le f (Nat.le_of_not_gt hn)
      rw [hone] at hcoeff
      exact False.elim (Int.one_ne_zero hcoeff)
  have hsize_le : f.size ≤ n + 1 := by
    by_cases hle : f.size ≤ n + 1
    · exact hle
    · have hlast_zero : f.coeff (f.size - 1) = 0 := by
        apply hhigh
        omega
      have hlast_ne : f.coeff (f.size - 1) ≠ 0 :=
        DensePoly.coeff_last_ne_zero_of_pos_size f (by omega)
      exact False.elim (hlast_ne hlast_zero)
  have hsize : f.size = n + 1 := by omega
  unfold DensePoly.Monic
  have hlast := coeff_last_eq_leadingCoeff f (by omega)
  rw [hsize] at hlast
  have hidx : n + 1 - 1 = n := by omega
  rw [hidx] at hlast
  rw [← hlast]
  exact hone

/-- `leadingCoeff_zero_mod_base` says a polynomial congruent to zero modulo `m` has leading coefficient divisible by `m`. -/
private theorem leadingCoeff_zero_mod_base
    (m : Nat) (f : ZPoly) (hf : ZPoly.congr f 0 m) :
    f.leadingCoeff % (m : Int) = 0 := by
  by_cases hpos : 0 < f.size
  · have hcoeff := hf (f.size - 1)
    rw [DensePoly.coeff_zero] at hcoeff
    rw [coeff_last_eq_leadingCoeff f hpos] at hcoeff
    simpa [Int.sub_zero] using hcoeff
  · have hsize : f.size = 0 := Nat.eq_zero_of_not_pos hpos
    have hlead : f.leadingCoeff = 0 := by
      cases f with
      | mk coeffs normalized =>
          simp only [DensePoly.leadingCoeff, DensePoly.size] at hsize ⊢
          simp [hsize, Array.getD] <;> rfl
    simp [hlead]

/-- `canonicalMod_congr_self` says canonical reduction differs from the original integer by a multiple of the modulus. -/
private theorem canonicalMod_congr_self
    (z : Int) (n : Nat) (hn : 0 < n) :
    (canonicalMod z n - z) % (n : Int) = 0 := by
  unfold canonicalMod
  have hnat :
      Int.ofNat (Int.toNat (z % (n : Int))) = z % (n : Int) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hn)))
  change (Int.ofNat (Int.toNat (z % (n : Int))) - z) % (n : Int) = 0
  rw [hnat]
  exact Int.emod_eq_zero_of_dvd (Int.dvd_sub_self_of_emod_eq rfl)

/-- `reduceCoeffModSquare_zero_mod_base` preserves divisibility by `m` when reducing a coefficient modulo `m²`. -/
private theorem reduceCoeffModSquare_zero_mod_base
    (m : Nat) (z : Int)
    (hz : z % (m : Int) = 0) :
    reduceCoeffModSquare z m % (m : Int) = 0 := by
  by_cases hm : m = 0
  · subst m
    simp [reduceCoeffModSquare, canonicalMod] at hz ⊢
    simp [hz]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hsqpos : 0 < m * m := Nat.mul_pos hmpos hmpos
    have hsq :
        (canonicalMod z (m * m) - z) % (((m * m : Nat) : Int)) = 0 :=
      canonicalMod_congr_self z (m * m) hsqpos
    have hz_dvd : (m : Int) ∣ z := Int.dvd_of_emod_eq_zero hz
    have hsq_dvd :
        ((m * m : Nat) : Int) ∣ canonicalMod z (m * m) - z :=
      Int.dvd_of_emod_eq_zero hsq
    have hm_dvd_sq : (m : Int) ∣ ((m * m : Nat) : Int) := by
      refine ⟨(m : Int), ?_⟩
      rw [Int.natCast_mul]
    have hm_dvd_diff : (m : Int) ∣ canonicalMod z (m * m) - z :=
      Int.dvd_trans hm_dvd_sq hsq_dvd
    have hm_dvd_canon : (m : Int) ∣ canonicalMod z (m * m) := by
      rcases hm_dvd_diff with ⟨a, ha⟩
      rcases hz_dvd with ⟨b, hb⟩
      refine ⟨a + b, ?_⟩
      calc
        canonicalMod z (m * m)
            = (canonicalMod z (m * m) - z) + z := by omega
        _ = (m : Int) * a + (m : Int) * b := by rw [ha, hb]
        _ = (m : Int) * (a + b) := by grind
    simpa [reduceCoeffModSquare, quadraticModulus] using
      Int.emod_eq_zero_of_dvd hm_dvd_canon

/-- `reduceModSquare_zero_mod_base` preserves polynomial congruence to zero modulo `m` after reduction modulo `m²`. -/
private theorem reduceModSquare_zero_mod_base
    (m : Nat) (f : ZPoly)
    (hf : ZPoly.congr f 0 m) :
    ZPoly.congr (QuadraticLiftResult.reduceModSquare f m) 0 m := by
  intro i
  by_cases hm : m = 0
  · subst m
    unfold QuadraticLiftResult.reduceModSquare
    have hfi : f.coeff i = 0 := by simpa using hf i
    rw [ZPoly.coeff_reduceModPow, DensePoly.coeff_zero, hfi]
    rfl
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hsq : ZPoly.congr (QuadraticLiftResult.reduceModSquare f m) f (m * m) :=
      reduceModSquare_congr m f hmpos
    have hsq_i :
        ((QuadraticLiftResult.reduceModSquare f m).coeff i - f.coeff i) %
            (((m * m : Nat) : Int)) = 0 :=
      hsq i
    have hdiff_dvd :
        ((m * m : Nat) : Int) ∣
          (QuadraticLiftResult.reduceModSquare f m).coeff i - f.coeff i :=
      Int.dvd_of_emod_eq_zero hsq_i
    have hm_dvd_sq : (m : Int) ∣ ((m * m : Nat) : Int) := by
      refine ⟨(m : Int), ?_⟩
      rw [Int.natCast_mul]
    have hm_dvd_diff :
        (m : Int) ∣ (QuadraticLiftResult.reduceModSquare f m).coeff i - f.coeff i :=
      Int.dvd_trans hm_dvd_sq hdiff_dvd
    have hf_i : (m : Int) ∣ f.coeff i := by
      exact Int.dvd_of_emod_eq_zero (by simpa using hf i)
    have hred_dvd : (m : Int) ∣ (QuadraticLiftResult.reduceModSquare f m).coeff i := by
      rcases hm_dvd_diff with ⟨a, ha⟩
      rcases hf_i with ⟨b, hb⟩
      refine ⟨a + b, ?_⟩
      calc
        (QuadraticLiftResult.reduceModSquare f m).coeff i
            =
              ((QuadraticLiftResult.reduceModSquare f m).coeff i - f.coeff i) +
                f.coeff i := by omega
        _ = (m : Int) * a + (m : Int) * b := by rw [ha, hb]
        _ = (m : Int) * (a + b) := by grind
    rw [DensePoly.coeff_zero]
    simpa using Int.emod_eq_zero_of_dvd hred_dvd

/-- `addModSquare_zero_mod_base` preserves congruence to zero modulo `m` for sums reduced modulo `m²`. -/
private theorem addModSquare_zero_mod_base
    (m : Nat) (f g : ZPoly)
    (hf : ZPoly.congr f 0 m) (hg : ZPoly.congr g 0 m) :
    ZPoly.congr (addModSquare f g m) 0 m := by
  unfold addModSquare
  apply reduceModSquare_zero_mod_base
  intro i
  rw [DensePoly.coeff_add]
  · have hfi : (f.coeff i) % (m : Int) = 0 := by simpa using hf i
    have hgi : (g.coeff i) % (m : Int) = 0 := by simpa using hg i
    simpa [Int.sub_zero] using
      Int.emod_eq_zero_of_dvd (Int.dvd_add
        (Int.dvd_of_emod_eq_zero hfi) (Int.dvd_of_emod_eq_zero hgi))
  · rfl

/-- `subModSquare_zero_mod_base` preserves congruence to zero modulo `m` for differences reduced modulo `m²`. -/
private theorem subModSquare_zero_mod_base
    (m : Nat) (f g : ZPoly)
    (hf : ZPoly.congr f 0 m) (hg : ZPoly.congr g 0 m) :
    ZPoly.congr (subModSquare f g m) 0 m := by
  unfold subModSquare
  apply reduceModSquare_zero_mod_base
  intro i
  rw [DensePoly.coeff_sub]
  · have hfi : (f.coeff i) % (m : Int) = 0 := by simpa using hf i
    have hgi : (g.coeff i) % (m : Int) = 0 := by simpa using hg i
    simpa [Int.sub_zero] using
      Int.emod_eq_zero_of_dvd (Int.dvd_sub
        (Int.dvd_of_emod_eq_zero hfi) (Int.dvd_of_emod_eq_zero hgi))
  · rfl

/-- `mulModSquare_left_zero_mod_base` preserves congruence to zero modulo `m` when the left factor is zero modulo `m`. -/
private theorem mulModSquare_left_zero_mod_base
    (m : Nat) (f g : ZPoly)
    (hf : ZPoly.congr f 0 m) :
    ZPoly.congr (mulModSquare f g m) 0 m := by
  unfold mulModSquare
  apply reduceModSquare_zero_mod_base
  simpa [DensePoly.zero_mul] using
    ZPoly.congr_mul f g 0 g m hf (ZPoly.congr_refl g m)

/-- `monomial_zero_mod_base` says a monomial is zero modulo `m` when its coefficient is divisible by `m`. -/
private theorem monomial_zero_mod_base
    (m k : Nat) (c : Int)
    (hc : c % (m : Int) = 0) :
    ZPoly.congr (DensePoly.monomial k c) 0 m := by
  intro i
  rw [DensePoly.coeff_monomial, DensePoly.coeff_zero]
  by_cases hi : i = k
  · simp [hi, hc]
  · rw [if_neg hi]
    change ((0 : Int) - 0) % (m : Int) = 0
    simp

/-- `divModMonicModSquareAux_zero_mod_base` preserves zero modulo `m` for the quotient and remainder produced by the division loop. -/
private theorem divModMonicModSquareAux_zero_mod_base
    (m : Nat) (q : ZPoly) (fuel : Nat) (quot rem qOut rOut : ZPoly)
    (hquot : ZPoly.congr quot 0 m)
    (hrem : ZPoly.congr rem 0 m)
    (hqr : (qOut, rOut) = divModMonicModSquareAux m q fuel quot rem) :
    ZPoly.congr qOut 0 m ∧ ZPoly.congr rOut 0 m := by
  induction fuel generalizing quot rem qOut rOut with
  | zero =>
      simp [divModMonicModSquareAux] at hqr
      rcases hqr with ⟨hqOut, hrOut⟩
      rw [hqOut, hrOut]
      exact ⟨hquot, hrem⟩
  | succ fuel ih =>
      cases hq : q.isZero with
      | true =>
          simp [divModMonicModSquareAux, hq] at hqr
          rcases hqr with ⟨hqOut, hrOut⟩
          rw [hqOut, hrOut]
          exact ⟨ZPoly.congr_refl 0 m, reduceModSquare_zero_mod_base m rem hrem⟩
      | false =>
          cases hremDeg : rem.degree? with
          | none =>
              simp [divModMonicModSquareAux, hq, hremDeg] at hqr
              rcases hqr with ⟨hqOut, hrOut⟩
              rw [hqOut, hrOut]
              exact ⟨hquot, hrem⟩
          | some rd =>
              cases hqdeg : q.degree? with
              | none =>
                  simp [divModMonicModSquareAux, hq, hremDeg, hqdeg] at hqr
                  rcases hqr with ⟨hqOut, hrOut⟩
                  rw [hqOut, hrOut]
                  exact ⟨hquot, hrem⟩
              | some qd =>
                  by_cases hlt : rd < qd
                  · simp [divModMonicModSquareAux, hq, hremDeg, hqdeg, hlt] at hqr
                    rcases hqr with ⟨hqOut, hrOut⟩
                    rw [hqOut, hrOut]
                    exact ⟨hquot, hrem⟩
                  · simp [divModMonicModSquareAux, hq, hremDeg, hqdeg, hlt] at hqr
                    let k := rd - qd
                    let coeff := reduceCoeffModSquare rem.leadingCoeff m
                    let term := DensePoly.monomial k coeff
                    have hcoeff : coeff % (m : Int) = 0 := by
                      exact reduceCoeffModSquare_zero_mod_base m rem.leadingCoeff
                        (leadingCoeff_zero_mod_base m rem hrem)
                    have hterm : ZPoly.congr term 0 m :=
                      monomial_zero_mod_base m k coeff hcoeff
                    have hquot' : ZPoly.congr (addModSquare quot term m) 0 m :=
                      addModSquare_zero_mod_base m quot term hquot hterm
                    have hmul : ZPoly.congr (mulModSquare term q m) 0 m :=
                      mulModSquare_left_zero_mod_base m term q hterm
                    have hrem' :
                        ZPoly.congr (subModSquare rem (mulModSquare term q m) m) 0 m :=
                      subModSquare_zero_mod_base m rem (mulModSquare term q m) hrem hmul
                    exact ih (addModSquare quot term m)
                      (subModSquare rem (mulModSquare term q m) m)
                      qOut rOut hquot' hrem' hqr

/-- `divModMonicModSquare_zero_mod_base` preserves zero modulo `m` for the quotient and remainder of monic modular division. -/
private theorem divModMonicModSquare_zero_mod_base
    (m : Nat) (p q qOut rOut : ZPoly)
    (hp : ZPoly.congr p 0 m)
    (hqr : (qOut, rOut) = divModMonicModSquare p q m) :
    ZPoly.congr qOut 0 m ∧ ZPoly.congr rOut 0 m := by
  unfold divModMonicModSquare at hqr
  let pRed := QuadraticLiftResult.reduceModSquare p m
  change (qOut, rOut) = divModMonicModSquareAux m q pRed.size 0 pRed at hqr
  exact divModMonicModSquareAux_zero_mod_base m q pRed.size 0 pRed qOut rOut
    (ZPoly.congr_refl 0 m)
    (reduceModSquare_zero_mod_base m p hp)
    hqr

/-- `monic_size_pos` says a monic polynomial has positive size. -/
private theorem monic_size_pos (q : ZPoly) (hmonic : DensePoly.Monic q) :
    0 < q.size := by
  by_cases hpos : 0 < q.size
  · exact hpos
  · have hsize : q.size = 0 := Nat.eq_zero_of_not_pos hpos
    have hlead : q.leadingCoeff = 0 := by
      cases q with
      | mk coeffs normalized =>
          simp only [DensePoly.leadingCoeff, DensePoly.size] at hsize ⊢
          simp [hsize, Array.getD] <;> rfl
    have hlead_one : q.leadingCoeff = 1 :=
      DensePoly.leadingCoeff_eq_one_of_monic hmonic
    rw [hlead] at hlead_one
    exact False.elim (Int.zero_ne_one hlead_one)

/-- `degree?_eq_some_size_sub_one` converts a successful optional degree into the corresponding polynomial size. -/
private theorem degree?_eq_some_size_sub_one
    (f : ZPoly) (d : Nat) (hdeg : f.degree? = some d) :
    f.size = d + 1 := by
  unfold DensePoly.degree? at hdeg
  by_cases hzero : f.size = 0
  · simp [hzero] at hdeg
  · simp [hzero] at hdeg
    omega

/-- `size_le_of_coeff_zero_from` bounds polynomial size when all coefficients from an index onward vanish. -/
private theorem size_le_of_coeff_zero_from
    (f : ZPoly) (n : Nat)
    (hzero : ∀ i, n ≤ i → f.coeff i = 0) :
    f.size ≤ n := by
  by_cases hle : f.size ≤ n
  · exact hle
  · have hlast_zero : f.coeff (f.size - 1) = 0 := hzero (f.size - 1) (by omega)
    have hlast_ne : f.coeff (f.size - 1) ≠ 0 :=
      DensePoly.coeff_last_ne_zero_of_pos_size f (by omega)
    exact False.elim (hlast_ne hlast_zero)

/-- `diagonalCoeffTerm` is the index-`i` contribution `p.coeff i * q.coeff (n - i)` to the degree-`n` coefficient of `p * q`, zero when `n < i`. -/
private def diagonalCoeffTerm (p q : ZPoly) (n i : Nat) : Int :=
  if n < i then 0 else p.coeff i * q.coeff (n - i)

/-- `fold_mulCoeffStep_eq_bounded_diagonal_int` evaluates the inner `mulCoeffStep` fold over `range m` to the accumulator plus the diagonal term when `i ≤ n` and `n - i < m`, and the accumulator alone otherwise. -/
private theorem fold_mulCoeffStep_eq_bounded_diagonal_int
    (p q : ZPoly) (n i m : Nat) (acc : Int) :
    (List.range m).foldl (DensePoly.mulCoeffStep p q n i) acc =
      acc + (if n < i then 0
        else if n - i < m then p.coeff i * q.coeff (n - i) else 0) := by
  induction m generalizing acc with
  | zero =>
      simp
  | succ m ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      unfold DensePoly.mulCoeffStep
      by_cases hlt : n < i
      · have hne : i + m ≠ n := by omega
        simp [hlt, hne]
      · by_cases hm : n - i < m
        · have hne : i + m ≠ n := by omega
          simp [hlt, hm, hne]
          grind
        · by_cases heq : i + m = n
          · have hsub : n - i = m := by omega
            simp [hlt, heq, hsub]
          · have hm' : ¬ n - i < m + 1 := by omega
            simp [hlt, hm, hm', heq]

/-- `fold_mulCoeffStep_eq_diagonal_int` collapses the inner `mulCoeffStep` fold over the full `range q.size` to the accumulator plus `diagonalCoeffTerm p q n i`. -/
private theorem fold_mulCoeffStep_eq_diagonal_int
    (p q : ZPoly) (n i : Nat) (acc : Int) :
    (List.range q.size).foldl (DensePoly.mulCoeffStep p q n i) acc =
      acc + diagonalCoeffTerm p q n i := by
  rw [fold_mulCoeffStep_eq_bounded_diagonal_int]
  unfold diagonalCoeffTerm
  by_cases hlt : n < i
  · simp [hlt]
  · by_cases hbound : n - i < q.size
    · simp [hlt, hbound]
    · have hcoeff : q.coeff (n - i) = 0 :=
        DensePoly.coeff_eq_zero_of_size_le q (Nat.le_of_not_gt hbound)
      simp [hlt, hbound, hcoeff]

/-- `fold_mulCoeff_outer_eq_diagonal_int` rewrites the outer coefficient fold so each inner `mulCoeffStep` loop becomes a single `diagonalCoeffTerm` accumulation. -/
private theorem fold_mulCoeff_outer_eq_diagonal_int
    (p q : ZPoly) (n : Nat) (xs : List Nat) (acc : Int) :
    xs.foldl (fun coeff i => (List.range q.size).foldl (DensePoly.mulCoeffStep p q n i) coeff) acc =
      xs.foldl (fun coeff i => coeff + diagonalCoeffTerm p q n i) acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [fold_mulCoeffStep_eq_diagonal_int]
      exact ih (acc + diagonalCoeffTerm p q n i)

/-- `mulCoeffSum_eq_diagonal_int` expresses the degree-`n` product coefficient as the fold of `diagonalCoeffTerm` over `range p.size`. -/
private theorem mulCoeffSum_eq_diagonal_int (p q : ZPoly) (n : Nat) :
    DensePoly.mulCoeffSum p q n =
      (List.range p.size).foldl (fun acc i => acc + diagonalCoeffTerm p q n i) 0 := by
  unfold DensePoly.mulCoeffSum
  exact fold_mulCoeff_outer_eq_diagonal_int p q n (List.range p.size) 0

/-- `fold_diagonal_monomial_left` collapses the diagonal fold for a degree-`k` monomial left factor to the single `k`-th term when `k < m`. -/
private theorem fold_diagonal_monomial_left
    (k : Nat) (c : Int) (q : ZPoly) (n m : Nat) :
    (List.range m).foldl
        (fun acc i => acc + diagonalCoeffTerm (DensePoly.monomial k c) q n i) 0 =
      if k < m then diagonalCoeffTerm (DensePoly.monomial k c) q n k else 0 := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      by_cases hk : k < m
      · have hmk : m ≠ k := by omega
        have hks : k < m + 1 := by omega
        have hterm : diagonalCoeffTerm (DensePoly.monomial k c) q n m = 0 := by
          unfold diagonalCoeffTerm
          by_cases hnm : n < m
          · simp [hnm]
          ·
            rw [DensePoly.coeff_monomial]
            simp [hnm, hmk]
            change (0 : Int) * q.coeff (n - m) = 0
            rw [Int.zero_mul]
        simp [hk, hks, hterm]
      · by_cases hmk : m = k
        · subst m
          have hkk : k < k + 1 := by omega
          simp [hkk]
        · have hks : ¬ k < m + 1 := by omega
          have hterm : diagonalCoeffTerm (DensePoly.monomial k c) q n m = 0 := by
            unfold diagonalCoeffTerm
            by_cases hnm : n < m
            · simp [hnm]
            ·
              rw [DensePoly.coeff_monomial]
              simp [hnm, hmk]
              change (0 : Int) * q.coeff (n - m) = 0
              rw [Int.zero_mul]
          simp [hk, hks, hterm]

/-- `coeff_monomial_mul` gives the degree-`n` coefficient of `monomial k c * q` as `c * q.coeff (n - k)`, zero when `n < k`. -/
private theorem coeff_monomial_mul
    (k : Nat) (c : Int) (q : ZPoly) (n : Nat) :
    ((DensePoly.monomial k c : ZPoly) * q).coeff n =
      if n < k then 0 else c * q.coeff (n - k) := by
  rw [DensePoly.coeff_mul, mulCoeffSum_eq_diagonal_int, fold_diagonal_monomial_left]
  by_cases hk : k < (DensePoly.monomial k c : ZPoly).size
  · simp [hk, diagonalCoeffTerm, DensePoly.coeff_monomial]
  · have hcoeff : (DensePoly.monomial k c : ZPoly).coeff k = 0 :=
      DensePoly.coeff_eq_zero_of_size_le (DensePoly.monomial k c : ZPoly)
        (Nat.le_of_not_gt hk)
    rw [DensePoly.coeff_monomial] at hcoeff
    have hc : c = 0 := by simpa using hcoeff
    subst c
    simp

private theorem coeff_mulModSquare_monomial_high
    (m k : Nat) (c : Int) (q : ZPoly) (n : Nat)
    (hhigh : q.size ≤ n - k) :
    (mulModSquare (DensePoly.monomial k c) q m).coeff n = 0 := by
  unfold mulModSquare QuadraticLiftResult.reduceModSquare
  apply ZPoly.coeff_reduceModPow_eq_zero_of_emod
  rw [coeff_monomial_mul]
  by_cases hnk : n < k
  · simp [hnk]
  · have hq : q.coeff (n - k) = 0 := DensePoly.coeff_eq_zero_of_size_le q hhigh
    simp [hnk, hq]

private theorem coeff_mulModSquare_monomial_leading
    (m k qd : Nat) (c : Int) (q : ZPoly)
    (hm : 0 < m)
    (hmonic : DensePoly.Monic q)
    (hqsize : q.size = qd + 1) :
    (mulModSquare (DensePoly.monomial k c) q m).coeff (k + qd) =
      c % Int.ofNat (m ^ 2) := by
  unfold mulModSquare QuadraticLiftResult.reduceModSquare
  rw [ZPoly.coeff_reduceModPow_eq_emod_of_pos, coeff_monomial_mul]
  have hnot : ¬ k + qd < k := by omega
  have hsub : k + qd - k = qd := by omega
  have hqpos : 0 < q.size := by omega
  have hqcoeff : q.coeff qd = 1 := by
    have hlast := coeff_last_eq_leadingCoeff q hqpos
    rw [hqsize] at hlast
    have hidx : qd + 1 - 1 = qd := by omega
    rw [hidx] at hlast
    rw [hlast]
    exact hmonic
  simp [hnot, hsub, hqcoeff]
  exact Nat.pow_pos hm

private theorem coeff_subModSquare_cancel_leading
    (m : Nat) (rem q : ZPoly) (rd qd : Nat)
    (hm : 0 < m)
    (hremSize : rem.size = rd + 1)
    (hqSize : q.size = qd + 1)
    (hmonic : DensePoly.Monic q)
    (hqd_le : qd ≤ rd) :
    (subModSquare rem
        (mulModSquare
          (DensePoly.monomial (rd - qd) (reduceCoeffModSquare rem.leadingCoeff m)) q m) m).coeff rd = 0 := by
  unfold subModSquare QuadraticLiftResult.reduceModSquare
  apply ZPoly.coeff_reduceModPow_eq_zero_of_emod
  rw [DensePoly.coeff_sub]
  · have hremLead : rem.coeff rd = rem.leadingCoeff := by
      have hpos : 0 < rem.size := by omega
      have hlast := coeff_last_eq_leadingCoeff rem hpos
      rw [hremSize] at hlast
      have hidx : rd + 1 - 1 = rd := by omega
      simpa [hidx] using hlast
    have hmul :
        (mulModSquare
          (DensePoly.monomial (rd - qd) (reduceCoeffModSquare rem.leadingCoeff m)) q m).coeff rd =
          (reduceCoeffModSquare rem.leadingCoeff m : Int) % Int.ofNat (m ^ 2) := by
      have hsum : rd - qd + qd = rd := by omega
      simpa [hsum] using
        coeff_mulModSquare_monomial_leading
          m (rd - qd) qd (reduceCoeffModSquare rem.leadingCoeff m) q hm hmonic hqSize
    rw [hremLead, hmul]
    unfold reduceCoeffModSquare canonicalMod quadraticModulus
    have hpow : m ^ 2 = m * m := by rw [Nat.pow_two]
    rw [hpow]
    have hnat :
        Int.ofNat (Int.toNat (rem.leadingCoeff % Int.ofNat (m * m))) =
          rem.leadingCoeff % Int.ofNat (m * m) := by
      have hpos : 0 < m * m := Nat.mul_pos hm hm
      exact Int.toNat_of_nonneg
        (Int.emod_nonneg _ (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hpos)))
    rw [hnat]
    have hemidem :
        rem.leadingCoeff % Int.ofNat (m * m) % Int.ofNat (m * m) =
          rem.leadingCoeff % Int.ofNat (m * m) := by
      rw [Int.emod_emod]
    rw [hemidem]
    exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hemidem.symm
  · rfl

private theorem divModMonicModSquare_step_remainder_size_le
    (m : Nat) (q rem : ZPoly) (rd qd fuel : Nat)
    (hm : 0 < m)
    (hremDeg : rem.degree? = some rd)
    (hqDeg : q.degree? = some qd)
    (hnotLt : ¬ rd < qd)
    (hmonic : DensePoly.Monic q)
    (hfuel : rem.size ≤ fuel + 1) :
    (subModSquare rem
        (mulModSquare
          (DensePoly.monomial (rd - qd) (reduceCoeffModSquare rem.leadingCoeff m)) q m) m).size ≤ fuel := by
  have hremSize : rem.size = rd + 1 :=
    degree?_eq_some_size_sub_one rem rd hremDeg
  have hqSize : q.size = qd + 1 :=
    degree?_eq_some_size_sub_one q qd hqDeg
  have hrd_le_fuel : rd ≤ fuel := by omega
  apply Nat.le_trans ?_ hrd_le_fuel
  apply size_le_of_coeff_zero_from
  intro i hi
  by_cases hir : i = rd
  · subst i
    exact coeff_subModSquare_cancel_leading m rem q rd qd hm hremSize hqSize hmonic
      (by omega)
  · have hgt : rd < i := by omega
    unfold subModSquare QuadraticLiftResult.reduceModSquare
    apply ZPoly.coeff_reduceModPow_eq_zero_of_emod
    rw [DensePoly.coeff_sub]
    · have hremCoeff : rem.coeff i = 0 :=
        DensePoly.coeff_eq_zero_of_size_le rem (by omega)
      have hmulCoeff :
          (mulModSquare
            (DensePoly.monomial (rd - qd) (reduceCoeffModSquare rem.leadingCoeff m)) q m).coeff i = 0 := by
        apply coeff_mulModSquare_monomial_high
        omega
      rw [hremCoeff, hmulCoeff]
      simp
    · rfl

private theorem divModMonicModSquareAux_remainder_coeff_eq_zero_of_monic
    (m : Nat)
    (q : ZPoly)
    (fuel : Nat)
    (quot rem qOut rOut : ZPoly)
    (_hm : 1 < m)
    (_hmonic : DensePoly.Monic q)
    (_hfuel : rem.size ≤ fuel)
    (_hqr : (qOut, rOut) = divModMonicModSquareAux m q fuel quot rem) :
    ∀ i, q.size - 1 ≤ i → rOut.coeff i = 0 := by
  induction fuel generalizing quot rem qOut rOut with
  | zero =>
      simp [divModMonicModSquareAux] at _hqr
      rcases _hqr with ⟨hqOut, hrOut⟩
      subst qOut
      subst rOut
      intro i _hi
      exact DensePoly.coeff_eq_zero_of_size_le rem (by omega)
  | succ fuel ih =>
      cases hq : q.isZero with
      | true =>
          have hqpos : 0 < q.size := monic_size_pos q _hmonic
          have hqsize0 : q.size = 0 := by
            simp [DensePoly.isZero] at hq
            simpa [DensePoly.size] using hq
          omega
      | false =>
          cases hremDeg : rem.degree? with
          | none =>
              simp [divModMonicModSquareAux, hq, hremDeg] at _hqr
              rcases _hqr with ⟨hqOut, hrOut⟩
              subst qOut
              subst rOut
              intro i _hi
              unfold DensePoly.degree? at hremDeg
              by_cases hzero : rem.size = 0
              · exact DensePoly.coeff_eq_zero_of_size_le rem (by omega)
              · simp [hzero] at hremDeg
          | some rd =>
              cases hqDeg : q.degree? with
              | none =>
                  have hqpos : 0 < q.size := monic_size_pos q _hmonic
                  unfold DensePoly.degree? at hqDeg
                  by_cases hzero : q.size = 0
                  · omega
                  · simp [hzero] at hqDeg
              | some qd =>
                  by_cases hlt : rd < qd
                  · simp [divModMonicModSquareAux, hq, hremDeg, hqDeg, hlt] at _hqr
                    rcases _hqr with ⟨hqOut, hrOut⟩
                    subst qOut
                    subst rOut
                    intro i hi
                    have hremSize : rem.size = rd + 1 :=
                      degree?_eq_some_size_sub_one rem rd hremDeg
                    have hqSize : q.size = qd + 1 :=
                      degree?_eq_some_size_sub_one q qd hqDeg
                    exact DensePoly.coeff_eq_zero_of_size_le rem (by omega)
                  · simp [divModMonicModSquareAux, hq, hremDeg, hqDeg, hlt] at _hqr
                    let k := rd - qd
                    let coeff := reduceCoeffModSquare rem.leadingCoeff m
                    let term := DensePoly.monomial k coeff
                    have hnextFuel :
                        (subModSquare rem (mulModSquare term q m) m).size ≤ fuel := by
                      exact divModMonicModSquare_step_remainder_size_le
                        m q rem rd qd fuel (by omega) hremDeg hqDeg hlt _hmonic _hfuel
                    exact ih (addModSquare quot term m)
                      (subModSquare rem (mulModSquare term q m) m)
                      qOut rOut hnextFuel _hqr

private theorem quadraticHenselStep_bezout_error_definition_congr
    (m : Nat) (s t g' h' b : ZPoly) (hm : 0 < m)
    (hb :
      b =
        subModSquare (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m) 1 m) :
    ZPoly.congr b (s * g' + t * h' - 1) (m * m) := by
  rw [hb]
  have hsg : ZPoly.congr (mulModSquare s g' m) (s * g') (m * m) :=
    mulModSquare_congr m s g' hm
  have hth : ZPoly.congr (mulModSquare t h' m) (t * h') (m * m) :=
    mulModSquare_congr m t h' hm
  have hadd₀ :
      ZPoly.congr
        (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m)
        (mulModSquare s g' m + mulModSquare t h' m)
        (m * m) :=
    addModSquare_congr m (mulModSquare s g' m) (mulModSquare t h' m) hm
  have hadd₁ :
      ZPoly.congr
        (mulModSquare s g' m + mulModSquare t h' m)
        (s * g' + t * h')
        (m * m) :=
    ZPoly.congr_add (mulModSquare s g' m) (mulModSquare t h' m) (s * g') (t * h')
      (m * m) hsg hth
  have hadd :
      ZPoly.congr
        (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m)
        (s * g' + t * h')
        (m * m) :=
    ZPoly.congr_trans _ _ _ (m * m) hadd₀ hadd₁
  have hsub₀ :
      ZPoly.congr
        (subModSquare (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m) 1 m)
        (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m - 1)
        (m * m) :=
    subModSquare_congr m
      (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m) 1 hm
  have hsub₁ :
      ZPoly.congr
        (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m - 1)
        (s * g' + t * h' - 1)
        (m * m) :=
    by
      intro i
      rw [DensePoly.coeff_sub, DensePoly.coeff_sub]
      · have hcoeff :
            DensePoly.coeff
                (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m) i -
                DensePoly.coeff (s * g' + t * h') i =
              DensePoly.coeff
                  (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m) i -
                  DensePoly.coeff (1 : ZPoly) i -
                (DensePoly.coeff (s * g' + t * h') i -
                  DensePoly.coeff (1 : ZPoly) i) := by
          omega
        rw [← hcoeff]
        exact hadd i
      · show (0 : Int) - (0 : Int) = 0
        omega
      · show (0 : Int) - (0 : Int) = 0
        omega
  exact
    ZPoly.congr_trans
      (subModSquare
        (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m) 1 m)
      (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m - 1)
      (s * g' + t * h' - 1)
      (m * m)
      hsub₀
      hsub₁

private theorem quadraticHenselStep_bezout_correction_exact
    (g h s t b q r : ZPoly) :
    ((s - s * b - q * h) * g + (t - r) * h) =
      (s * g + t * h) - (s * b * g + (q * g + r) * h) := by
  calc
    ((s - s * b - q * h) * g + (t - r) * h)
        = ((s - s * b) * g + (0 - q * h) * g) + (t - r) * h := by
          rw [DensePoly.sub_eq_add_neg_poly (s - s * b) (q * h), DensePoly.mul_add_left_poly]
    _ = ((s * g + (0 - s * b) * g) + (0 - q * h) * g) + (t - r) * h := by
          rw [DensePoly.sub_eq_add_neg_poly s (s * b), DensePoly.mul_add_left_poly]
    _ = ((s * g + (0 - s * b * g)) + (0 - (q * h) * g)) + (t - r) * h := by
          rw [DensePoly.neg_mul_right_poly (s * b) g, DensePoly.neg_mul_right_poly (q * h) g]
    _ = ((s * g + (0 - s * b * g)) + (0 - (q * g) * h)) + (t - r) * h := by
          rw [DensePoly.mul_assoc_poly q h g, DensePoly.mul_comm_poly h g,
            ← DensePoly.mul_assoc_poly q g h]
    _ = ((s * g + (0 - s * b * g)) + (0 - (q * g) * h)) +
          (t * h + (0 - r) * h) := by
          rw [DensePoly.sub_eq_add_neg_poly t r, DensePoly.mul_add_left_poly]
    _ = ((s * g + (0 - s * b * g)) + (0 - (q * g) * h)) +
          (t * h + (0 - r * h)) := by
          rw [DensePoly.neg_mul_right_poly r h]
    _ = (s * g + t * h) + (0 - (s * b * g + ((q * g) * h + r * h))) := by
          apply DensePoly.ext_coeff
          intro n
          repeat
            first
            | rw [DensePoly.coeff_add]
            | rw [DensePoly.coeff_sub]
            | rw [DensePoly.coeff_zero]
          all_goals try rfl
          omega
    _ = (s * g + t * h) + (0 - (s * b * g + (q * g + r) * h)) := by
          rw [DensePoly.mul_add_left_poly]
    _ = (s * g + t * h) - (s * b * g + (q * g + r) * h) := by
          exact (DensePoly.sub_eq_add_neg_poly
            (s * g + t * h) (s * b * g + (q * g + r) * h)).symm

private theorem quadraticHenselStep_bezout_mul_error_exact
    (g h s t b : ZPoly) :
    s * b * g + (t * b) * h = b * (s * g + t * h) := by
  calc
    s * b * g + (t * b) * h
        = b * s * g + (t * b) * h := by
          rw [DensePoly.mul_comm_poly s b]
    _ = b * s * g + b * t * h := by
          rw [DensePoly.mul_comm_poly t b]
    _ = b * (s * g) + b * t * h := by
          rw [DensePoly.mul_assoc_poly b s g]
    _ = b * (s * g) + b * (t * h) := by
          rw [DensePoly.mul_assoc_poly b t h]
    _ = b * (s * g + t * h) := by
          rw [← DensePoly.mul_add_right_poly b (s * g) (t * h)]

private theorem quadraticHenselStep_sub_one_add_one_exact
    (x : ZPoly) :
    (x - 1) + 1 = x := by
  apply DensePoly.ext_coeff
  intro n
  repeat
    first
    | rw [DensePoly.coeff_add]
    | rw [DensePoly.coeff_sub]
    | rw [DensePoly.coeff_zero]
  all_goals try rfl
  omega

private theorem quadraticHenselStep_one_sub_error_exact
    (b : ZPoly) :
    (b + 1) - b * (b + 1) = 1 - b * b := by
  calc
    (b + 1) - b * (b + 1)
        = (b + 1) - (b * b + b * 1) := by
          rw [DensePoly.mul_add_right_poly]
    _ = (b + 1) - (b * b + b) := by
          rw [DensePoly.mul_one_right_poly]
    _ = 1 + (0 - b * b) := by
          rw [DensePoly.add_sub_add_swap b 1 (b * b)]
    _ = 1 - b * b := by
          exact (DensePoly.sub_eq_add_neg_poly 1 (b * b)).symm

private theorem quadraticHenselStep_bezout_correction_algebra
    (m : Nat)
    (g' h' s t b qBezout rBezout : ZPoly)
    (hm : 0 < m)
    (hb : ZPoly.congr b (s * g' + t * h' - 1) (m * m))
    (hdiv : ZPoly.congr (qBezout * g' + rBezout) (t * b) (m * m)) :
    let t' := subModSquare t rBezout m
    let s' := subModSquare (subModSquare s (mulModSquare s b m) m) (mulModSquare qBezout h' m) m
    ZPoly.congr (s' * g' + t' * h') (1 - b * b) (m * m) := by
  intro t' s'
  have hsb :
      ZPoly.congr (mulModSquare s b m) (s * b) (m * m) :=
    mulModSquare_congr m s b hm
  have hsMinus :
      ZPoly.congr
        (subModSquare s (mulModSquare s b m) m)
        (s - s * b)
        (m * m) := by
    have hred :
        ZPoly.congr
          (subModSquare s (mulModSquare s b m) m)
          (s - mulModSquare s b m)
          (m * m) :=
      subModSquare_congr m s (mulModSquare s b m) hm
    have hplain :
        ZPoly.congr (s - mulModSquare s b m) (s - s * b) (m * m) :=
      congr_sub s (mulModSquare s b m) s (s * b) (m * m)
        (ZPoly.congr_refl s (m * m)) hsb
    exact ZPoly.congr_trans _ _ _ (m * m) hred hplain
  have hqh :
      ZPoly.congr (mulModSquare qBezout h' m) (qBezout * h') (m * m) :=
    mulModSquare_congr m qBezout h' hm
  have hs' :
      ZPoly.congr s' (s - s * b - qBezout * h') (m * m) := by
    have hred :
        ZPoly.congr
          (subModSquare
            (subModSquare s (mulModSquare s b m) m)
            (mulModSquare qBezout h' m) m)
          (subModSquare s (mulModSquare s b m) m - mulModSquare qBezout h' m)
          (m * m) :=
      subModSquare_congr m
        (subModSquare s (mulModSquare s b m) m)
        (mulModSquare qBezout h' m) hm
    have hplain :
        ZPoly.congr
          (subModSquare s (mulModSquare s b m) m - mulModSquare qBezout h' m)
          (s - s * b - qBezout * h')
          (m * m) :=
      congr_sub
        (subModSquare s (mulModSquare s b m) m)
        (mulModSquare qBezout h' m)
        (s - s * b)
        (qBezout * h')
        (m * m)
        hsMinus
        hqh
    exact ZPoly.congr_trans s'
      (subModSquare s (mulModSquare s b m) m - mulModSquare qBezout h' m)
      (s - s * b - qBezout * h')
      (m * m)
      (by simpa [s'] using hred)
      hplain
  have ht' : ZPoly.congr t' (t - rBezout) (m * m) :=
    by simpa [t'] using subModSquare_congr m t rBezout hm
  have hleft :
      ZPoly.congr
        (s' * g' + t' * h')
        ((s - s * b - qBezout * h') * g' + (t - rBezout) * h')
        (m * m) :=
    ZPoly.congr_add (s' * g') (t' * h')
      ((s - s * b - qBezout * h') * g') ((t - rBezout) * h')
      (m * m)
      (ZPoly.congr_mul s' g' (s - s * b - qBezout * h') g'
        (m * m) hs' (ZPoly.congr_refl g' (m * m)))
      (ZPoly.congr_mul t' h' (t - rBezout) h'
        (m * m) ht' (ZPoly.congr_refl h' (m * m)))
  let a := s * g' + t * h'
  have hnormalized :
      ((s - s * b - qBezout * h') * g' + (t - rBezout) * h') =
        a - (s * b * g' + (qBezout * g' + rBezout) * h') := by
    simpa [a] using
      quadraticHenselStep_bezout_correction_exact
        g' h' s t b qBezout rBezout
  have hdivH :
      ZPoly.congr
        ((qBezout * g' + rBezout) * h')
        ((t * b) * h')
        (m * m) :=
    ZPoly.congr_mul (qBezout * g' + rBezout) h' (t * b) h'
      (m * m) hdiv (ZPoly.congr_refl h' (m * m))
  have hsecond :
      ZPoly.congr
        (s * b * g' + (qBezout * g' + rBezout) * h')
        (b * a)
        (m * m) := by
    have hsum :
        ZPoly.congr
          (s * b * g' + (qBezout * g' + rBezout) * h')
          (s * b * g' + (t * b) * h')
          (m * m) :=
      ZPoly.congr_add (s * b * g') ((qBezout * g' + rBezout) * h')
        (s * b * g') ((t * b) * h')
        (m * m)
        (ZPoly.congr_refl (s * b * g') (m * m))
        hdivH
    have hexact :
        s * b * g' + (t * b) * h' = b * a := by
      simpa [a] using quadraticHenselStep_bezout_mul_error_exact g' h' s t b
    exact ZPoly.congr_trans _ _ _ (m * m) hsum
      (by simpa [hexact] using ZPoly.congr_refl (s * b * g' + (t * b) * h') (m * m))
  have ha : ZPoly.congr a (b + 1) (m * m) := by
    have hadd :
        ZPoly.congr (b + 1) ((a - 1) + 1) (m * m) :=
      ZPoly.congr_add b 1 (a - 1) 1 (m * m) hb (ZPoly.congr_refl 1 (m * m))
    exact ZPoly.congr_symm _ _ _ <|
      ZPoly.congr_trans (b + 1) ((a - 1) + 1) a (m * m) hadd
        (by
          simpa [quadraticHenselStep_sub_one_add_one_exact a] using
            ZPoly.congr_refl ((a - 1) + 1) (m * m))
  have hright :
      ZPoly.congr
        (a - (s * b * g' + (qBezout * g' + rBezout) * h'))
        ((b + 1) - b * (b + 1))
        (m * m) := by
    exact congr_sub a (s * b * g' + (qBezout * g' + rBezout) * h')
      (b + 1) (b * (b + 1)) (m * m)
      ha
      (ZPoly.congr_trans _ _ _ (m * m) hsecond
        (congr_mul_left b a (b + 1) (m * m) ha))
  exact ZPoly.congr_trans
    (s' * g' + t' * h')
    (a - (s * b * g' + (qBezout * g' + rBezout) * h'))
    (1 - b * b)
    (m * m)
    (ZPoly.congr_trans _ _ _ (m * m) hleft
      (by
        simpa [hnormalized] using
          ZPoly.congr_refl
            ((s - s * b - qBezout * h') * g' + (t - rBezout) * h')
            (m * m)))
    (ZPoly.congr_trans _ _ _ (m * m) hright
      (by
        simpa [quadraticHenselStep_one_sub_error_exact b] using
          ZPoly.congr_refl ((b + 1) - b * (b + 1)) (m * m)))

private theorem quadraticHenselStep_bezout_error_from_factor_update
    (m : Nat)
    (f g h s t : ZPoly)
    (hm : 1 < m)
    (hprod : ZPoly.congr (g * h) f m)
    (hbez : ZPoly.congr (s * g + t * h) 1 m)
    (_hmonic : DensePoly.Monic g) :
    let e := QuadraticLiftResult.factorError f g h
    let te := mulModSquare t e m
    let factorQR := divModMonicModSquare te g m
    let qFactor := factorQR.1
    let rFactor := factorQR.2
    let g' := addModSquare g rFactor m
    let hCorrection := addModSquare (mulModSquare s e m) (mulModSquare qFactor h m) m
    let h' := addModSquare h hCorrection m
    let b := subModSquare (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m) 1 m
    ZPoly.congr b 0 m := by
  intro e te factorQR qFactor rFactor g' hCorrection h' b
  have hm0 : 0 < m := Nat.lt_trans Nat.zero_lt_one hm
  have he : ZPoly.congr e 0 m := by
    have hf : ZPoly.congr f (g * h) m := ZPoly.congr_symm (g * h) f m hprod
    simpa [e, QuadraticLiftResult.factorError, sub_self_eq_zero (g * h)] using
      congr_sub f (g * h) (g * h) (g * h) m hf (ZPoly.congr_refl (g * h) m)
  have hte : ZPoly.congr te 0 m := by
    have hmul : ZPoly.congr (mulModSquare t e m) (t * e) (m * m) :=
      mulModSquare_congr m t e hm0
    have hmulBase : ZPoly.congr (t * e) 0 m := by
      exact mul_right_zero_mod_base m t e he
    exact ZPoly.congr_trans te (t * e) 0 m
      (congr_of_square_mod m te (t * e) (by simpa [te] using hmul)) hmulBase
  have hpair : (qFactor, rFactor) = divModMonicModSquare te g m := by
    simp [factorQR, qFactor, rFactor]
  have hqr : ZPoly.congr qFactor 0 m ∧ ZPoly.congr rFactor 0 m :=
    divModMonicModSquare_zero_mod_base m te g qFactor rFactor hte hpair
  have hg' : ZPoly.congr g' g m := by
    have hadd : ZPoly.congr (addModSquare g rFactor m) (g + rFactor) (m * m) :=
      addModSquare_congr m g rFactor hm0
    have hbase : ZPoly.congr (g + rFactor) (g + 0) m :=
      ZPoly.congr_add g rFactor g 0 m (ZPoly.congr_refl g m) hqr.2
    have hzero : (g + (0 : ZPoly)) = g := by
      apply DensePoly.ext_coeff
      intro i
      rw [DensePoly.coeff_add, DensePoly.coeff_zero]
      · omega
      · rfl
    exact ZPoly.congr_trans g' (g + rFactor) g m
      (congr_of_square_mod m g' (g + rFactor) (by simpa [g'] using hadd))
      (by simpa [hzero] using hbase)
  have hCorrection_zero : ZPoly.congr hCorrection 0 m := by
    have hseSq : ZPoly.congr (mulModSquare s e m) (s * e) (m * m) :=
      mulModSquare_congr m s e hm0
    have hse : ZPoly.congr (mulModSquare s e m) 0 m := by
      have hmulBase : ZPoly.congr (s * e) 0 m := by
        exact mul_right_zero_mod_base m s e he
      exact ZPoly.congr_trans (mulModSquare s e m) (s * e) 0 m
        (congr_of_square_mod m (mulModSquare s e m) (s * e) hseSq) hmulBase
    have hqhSq : ZPoly.congr (mulModSquare qFactor h m) (qFactor * h) (m * m) :=
      mulModSquare_congr m qFactor h hm0
    have hqh : ZPoly.congr (mulModSquare qFactor h m) 0 m := by
      have hmulBase : ZPoly.congr (qFactor * h) 0 m := by
        simpa [DensePoly.zero_mul] using
          ZPoly.congr_mul qFactor h 0 h m hqr.1 (ZPoly.congr_refl h m)
      exact ZPoly.congr_trans (mulModSquare qFactor h m) (qFactor * h) 0 m
        (congr_of_square_mod m (mulModSquare qFactor h m) (qFactor * h) hqhSq) hmulBase
    have hadd :
        ZPoly.congr
          (addModSquare (mulModSquare s e m) (mulModSquare qFactor h m) m)
          (mulModSquare s e m + mulModSquare qFactor h m)
          (m * m) :=
      addModSquare_congr m (mulModSquare s e m) (mulModSquare qFactor h m) hm0
    have hsum : ZPoly.congr (mulModSquare s e m + mulModSquare qFactor h m) 0 m := by
      simpa [DensePoly.zero_add] using
        ZPoly.congr_add (mulModSquare s e m) (mulModSquare qFactor h m) 0 0 m hse hqh
    exact ZPoly.congr_trans hCorrection
      (mulModSquare s e m + mulModSquare qFactor h m) 0 m
      (congr_of_square_mod m hCorrection
        (mulModSquare s e m + mulModSquare qFactor h m)
        (by simpa [hCorrection] using hadd))
      hsum
  have hh' : ZPoly.congr h' h m := by
    have hadd : ZPoly.congr (addModSquare h hCorrection m) (h + hCorrection) (m * m) :=
      addModSquare_congr m h hCorrection hm0
    have hbase : ZPoly.congr (h + hCorrection) (h + 0) m :=
      ZPoly.congr_add h hCorrection h 0 m (ZPoly.congr_refl h m) hCorrection_zero
    have hzero : (h + (0 : ZPoly)) = h := by
      apply DensePoly.ext_coeff
      intro i
      rw [DensePoly.coeff_add, DensePoly.coeff_zero]
      · omega
      · rfl
    exact ZPoly.congr_trans h' (h + hCorrection) h m
      (congr_of_square_mod m h' (h + hCorrection) (by simpa [h'] using hadd))
      (by simpa [hzero] using hbase)
  have hsg : ZPoly.congr (mulModSquare s g' m) (s * g) m := by
    have hsq : ZPoly.congr (mulModSquare s g' m) (s * g') (m * m) :=
      mulModSquare_congr m s g' hm0
    exact ZPoly.congr_trans (mulModSquare s g' m) (s * g') (s * g) m
      (congr_of_square_mod m (mulModSquare s g' m) (s * g') hsq)
      (ZPoly.congr_mul s g' s g m (ZPoly.congr_refl s m) hg')
  have hth : ZPoly.congr (mulModSquare t h' m) (t * h) m := by
    have hsq : ZPoly.congr (mulModSquare t h' m) (t * h') (m * m) :=
      mulModSquare_congr m t h' hm0
    exact ZPoly.congr_trans (mulModSquare t h' m) (t * h') (t * h) m
      (congr_of_square_mod m (mulModSquare t h' m) (t * h') hsq)
      (ZPoly.congr_mul t h' t h m (ZPoly.congr_refl t m) hh')
  have haddInner :
      ZPoly.congr
        (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m)
        (s * g + t * h)
        m := by
    have haddSq :
        ZPoly.congr
          (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m)
          (mulModSquare s g' m + mulModSquare t h' m)
          (m * m) :=
      addModSquare_congr m (mulModSquare s g' m) (mulModSquare t h' m) hm0
    have haddBase :
        ZPoly.congr
          (mulModSquare s g' m + mulModSquare t h' m)
          (s * g + t * h)
          m :=
      ZPoly.congr_add (mulModSquare s g' m) (mulModSquare t h' m)
        (s * g) (t * h) m hsg hth
    exact ZPoly.congr_trans
      (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m)
      (mulModSquare s g' m + mulModSquare t h' m)
      (s * g + t * h) m
      (congr_of_square_mod m
        (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m)
        (mulModSquare s g' m + mulModSquare t h' m)
        haddSq)
      haddBase
  have hbToError :
      ZPoly.congr b (s * g + t * h - 1) m := by
    have hsubSq :
        ZPoly.congr
          (subModSquare
            (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m) 1 m)
          (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m - 1)
          (m * m) :=
      subModSquare_congr m
        (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m) 1 hm0
    exact ZPoly.congr_trans b
      (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m - 1)
      (s * g + t * h - 1)
      m
      (congr_of_square_mod m b
        (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m - 1)
        (by simpa [b] using hsubSq))
      (congr_sub
        (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m) 1
        (s * g + t * h) 1 m haddInner (ZPoly.congr_refl 1 m))
  have htarget : ZPoly.congr (s * g + t * h - 1) 0 m := by
    have key := congr_sub (s * g + t * h) 1 1 1 m hbez (ZPoly.congr_refl 1 m)
    rw [sub_self_eq_zero] at key
    exact key
  exact ZPoly.congr_trans b (s * g + t * h - 1) 0 m hbToError htarget

private theorem quadraticHenselStep_bezout_correction_congr_core
    (m : Nat)
    (g' h' s t b qBezout rBezout : ZPoly)
    (hm : 1 < m)
    (hb : ZPoly.congr b (s * g' + t * h' - 1) (m * m))
    (hbezoutQR :
      let tb := mulModSquare t b m
      let bezoutQR := divModMonicModSquare tb g' m
      qBezout = bezoutQR.1 ∧ rBezout = bezoutQR.2) :
    let t' := subModSquare t rBezout m
    let s' := subModSquare (subModSquare s (mulModSquare s b m) m) (mulModSquare qBezout h' m) m
    ZPoly.congr (s' * g' + t' * h') (1 - b * b) (m * m) := by
  have hm0 : 0 < m := Nat.lt_trans Nat.zero_lt_one hm
  let tb := mulModSquare t b m
  let bezoutQR := divModMonicModSquare tb g' m
  have hpair : (qBezout, rBezout) = bezoutQR := by
    rcases hbezoutQR with ⟨hq, hr⟩
    exact Prod.ext hq hr
  have hdivMod :
      ZPoly.congr (qBezout * g' + rBezout) tb (m * m) :=
    divModMonicModSquare_reconstruct_congr m tb g' qBezout rBezout hm0 hpair
  have hmul : ZPoly.congr tb (t * b) (m * m) :=
    mulModSquare_congr m t b hm0
  have hdiv : ZPoly.congr (qBezout * g' + rBezout) (t * b) (m * m) :=
    ZPoly.congr_trans (qBezout * g' + rBezout) tb (t * b) (m * m) hdivMod hmul
  simpa [tb] using
    quadraticHenselStep_bezout_correction_algebra
      m g' h' s t b qBezout rBezout hm0 hb hdiv

/-- If `b ≡ 0 (mod m)` then `m²` divides the product `b.coeff i * b.coeff j` of
any two of its coefficients. -/
private theorem coeff_product_dvd_mod_square
    (m : Nat) (b : ZPoly)
    (hb : ZPoly.congr b 0 m) (i j : Nat) :
    ((m * m : Nat) : Int) ∣ b.coeff i * b.coeff j := by
  have hi_mod : (b.coeff i) % (m : Int) = 0 := by
    simpa using hb i
  have hj_mod : (b.coeff j) % (m : Int) = 0 := by
    simpa using hb j
  rcases Int.dvd_of_emod_eq_zero hi_mod with ⟨ai, hai⟩
  rcases Int.dvd_of_emod_eq_zero hj_mod with ⟨aj, haj⟩
  refine ⟨ai * aj, ?_⟩
  calc
    b.coeff i * b.coeff j
        = ((m : Int) * ai) * ((m : Int) * aj) := by rw [← hai, ← haj]
    _ = ((m * m : Nat) : Int) * (ai * aj) := by
          grind

/-- One `DensePoly.mulCoeffStep b b` accumulation stays divisible by `m²` when
`b ≡ 0 (mod m)` and the incoming accumulator is already divisible by `m²`. -/
private theorem mulCoeffStep_dvd_mod_square
    (m : Nat) (b : ZPoly)
    (hb : ZPoly.congr b 0 m) (n i : Nat) (acc : Int) (j : Nat)
    (hacc : ((m * m : Nat) : Int) ∣ acc) :
    ((m * m : Nat) : Int) ∣ DensePoly.mulCoeffStep b b n i acc j := by
  by_cases hij : i + j = n
  · rcases hacc with ⟨a, ha⟩
    rcases coeff_product_dvd_mod_square m b hb i j with ⟨c, hc⟩
    refine ⟨a + c, ?_⟩
    calc
      DensePoly.mulCoeffStep b b n i acc j
          = acc + b.coeff i * b.coeff j := by simp [DensePoly.mulCoeffStep, hij]
      _ = ((m * m : Nat) : Int) * a + ((m * m : Nat) : Int) * c := by rw [ha, hc]
      _ = ((m * m : Nat) : Int) * (a + c) := by grind
  · simpa [DensePoly.mulCoeffStep, hij] using hacc

/-- Folding `DensePoly.mulCoeffStep b b n i` over `xs` preserves divisibility by
`m²` when `b ≡ 0 (mod m)` and the starting accumulator is divisible by `m²`. -/
private theorem foldl_mulCoeffStep_dvd_mod_square
    (m : Nat) (b : ZPoly)
    (hb : ZPoly.congr b 0 m) (n i : Nat) (xs : List Nat) (acc : Int)
    (hacc : ((m * m : Nat) : Int) ∣ acc) :
    ((m * m : Nat) : Int) ∣
      xs.foldl (DensePoly.mulCoeffStep b b n i) acc := by
  induction xs generalizing acc with
  | nil =>
      simpa using hacc
  | cons j xs ih =>
      simpa using
        ih (DensePoly.mulCoeffStep b b n i acc j)
          (mulCoeffStep_dvd_mod_square m b hb n i acc j hacc)

/-- The outer `mulCoeffSum` fold for `b * b` preserves divisibility by `m²` when
`b ≡ 0 (mod m)` and the starting accumulator is divisible by `m²`. -/
private theorem foldl_mulCoeffSum_dvd_mod_square
    (m : Nat) (b : ZPoly)
    (hb : ZPoly.congr b 0 m) (n : Nat) (xs : List Nat) (acc : Int)
    (hacc : ((m * m : Nat) : Int) ∣ acc) :
    ((m * m : Nat) : Int) ∣
      xs.foldl
        (fun acc i => (List.range b.size).foldl (DensePoly.mulCoeffStep b b n i) acc)
        acc := by
  induction xs generalizing acc with
  | nil =>
      simpa using hacc
  | cons i xs ih =>
      have hinner :
          ((m * m : Nat) : Int) ∣
            (List.range b.size).foldl (DensePoly.mulCoeffStep b b n i) acc :=
        foldl_mulCoeffStep_dvd_mod_square m b hb n i (List.range b.size) acc hacc
      simpa using ih
        ((List.range b.size).foldl (DensePoly.mulCoeffStep b b n i) acc) hinner

/-- If `b ≡ 0 (mod m)` then its square satisfies `b * b ≡ 0 (mod m²)`. -/
private theorem square_congr_zero_mod_square
    (m : Nat) (b : ZPoly)
    (_hm : 1 < m)
    (hb : ZPoly.congr b 0 m) :
    ZPoly.congr (b * b) 0 (m * m) := by
  intro n
  have hdvd :
      ((m * m : Nat) : Int) ∣ (b * b).coeff n := by
    rw [DensePoly.coeff_mul, DensePoly.mulCoeffSum]
    exact foldl_mulCoeffSum_dvd_mod_square m b hb n (List.range b.size) 0 ⟨0, by simp⟩
  simpa using Int.emod_eq_zero_of_dvd hdvd

/-- If both `a ≡ 0 (mod m)` and `b ≡ 0 (mod m)` then `m²` divides the cross
product `a.coeff i * b.coeff j`. -/
private theorem coeff_product_dvd_mod_square_of_congr_zero
    (m : Nat) (a b : ZPoly)
    (ha : ZPoly.congr a 0 m) (hb : ZPoly.congr b 0 m) (i j : Nat) :
    ((m * m : Nat) : Int) ∣ a.coeff i * b.coeff j := by
  have hi_mod : (a.coeff i) % (m : Int) = 0 := by
    simpa using ha i
  have hj_mod : (b.coeff j) % (m : Int) = 0 := by
    simpa using hb j
  rcases Int.dvd_of_emod_eq_zero hi_mod with ⟨ai, hai⟩
  rcases Int.dvd_of_emod_eq_zero hj_mod with ⟨bj, hbj⟩
  refine ⟨ai * bj, ?_⟩
  calc
    a.coeff i * b.coeff j
        = ((m : Int) * ai) * ((m : Int) * bj) := by rw [← hai, ← hbj]
    _ = ((m * m : Nat) : Int) * (ai * bj) := by
          grind

/-- Two-factor form of `mulCoeffStep_dvd_mod_square`: one `DensePoly.mulCoeffStep
a b` accumulation stays divisible by `m²` when both `a ≡ 0 (mod m)` and
`b ≡ 0 (mod m)` and the incoming accumulator is divisible by `m²`. -/
private theorem mulCoeffStep_dvd_mod_square_of_congr_zero
    (m : Nat) (a b : ZPoly)
    (ha : ZPoly.congr a 0 m) (hb : ZPoly.congr b 0 m)
    (n i : Nat) (acc : Int) (j : Nat)
    (hacc : ((m * m : Nat) : Int) ∣ acc) :
    ((m * m : Nat) : Int) ∣ DensePoly.mulCoeffStep a b n i acc j := by
  by_cases hij : i + j = n
  · rcases hacc with ⟨c, hc⟩
    rcases coeff_product_dvd_mod_square_of_congr_zero m a b ha hb i j with ⟨d, hd⟩
    refine ⟨c + d, ?_⟩
    calc
      DensePoly.mulCoeffStep a b n i acc j
          = acc + a.coeff i * b.coeff j := by simp [DensePoly.mulCoeffStep, hij]
      _ = ((m * m : Nat) : Int) * c + ((m * m : Nat) : Int) * d := by rw [hc, hd]
      _ = ((m * m : Nat) : Int) * (c + d) := by grind
  · simpa [DensePoly.mulCoeffStep, hij] using hacc

/-- Two-factor form of `foldl_mulCoeffStep_dvd_mod_square`: folding
`DensePoly.mulCoeffStep a b n i` over `xs` preserves divisibility by `m²` when
both `a ≡ 0 (mod m)` and `b ≡ 0 (mod m)` and the starting accumulator is
divisible by `m²`. -/
private theorem foldl_mulCoeffStep_dvd_mod_square_of_congr_zero
    (m : Nat) (a b : ZPoly)
    (ha : ZPoly.congr a 0 m) (hb : ZPoly.congr b 0 m)
    (n i : Nat) (xs : List Nat) (acc : Int)
    (hacc : ((m * m : Nat) : Int) ∣ acc) :
    ((m * m : Nat) : Int) ∣
      xs.foldl (DensePoly.mulCoeffStep a b n i) acc := by
  induction xs generalizing acc with
  | nil =>
      simpa using hacc
  | cons j xs ih =>
      simpa using
        ih (DensePoly.mulCoeffStep a b n i acc j)
          (mulCoeffStep_dvd_mod_square_of_congr_zero m a b ha hb n i acc j hacc)

/-- Two-factor form of `foldl_mulCoeffSum_dvd_mod_square`: the outer
`mulCoeffSum` fold for `a * b` preserves divisibility by `m²` when both
`a ≡ 0 (mod m)` and `b ≡ 0 (mod m)` and the starting accumulator is divisible by
`m²`. -/
private theorem foldl_mulCoeffSum_dvd_mod_square_of_congr_zero
    (m : Nat) (a b : ZPoly)
    (ha : ZPoly.congr a 0 m) (hb : ZPoly.congr b 0 m)
    (n : Nat) (xs : List Nat) (acc : Int)
    (hacc : ((m * m : Nat) : Int) ∣ acc) :
    ((m * m : Nat) : Int) ∣
      xs.foldl
        (fun acc i => (List.range b.size).foldl (DensePoly.mulCoeffStep a b n i) acc)
        acc := by
  induction xs generalizing acc with
  | nil =>
      simpa using hacc
  | cons i xs ih =>
      have hinner :
          ((m * m : Nat) : Int) ∣
            (List.range b.size).foldl (DensePoly.mulCoeffStep a b n i) acc :=
        foldl_mulCoeffStep_dvd_mod_square_of_congr_zero
          m a b ha hb n i (List.range b.size) acc hacc
      simpa using ih
        ((List.range b.size).foldl (DensePoly.mulCoeffStep a b n i) acc) hinner

private theorem mul_congr_zero_mod_square_of_congr_zero
    (m : Nat) (a b : ZPoly)
    (ha : ZPoly.congr a 0 m) (hb : ZPoly.congr b 0 m) :
    ZPoly.congr (a * b) 0 (m * m) := by
  intro n
  have hdvd :
      ((m * m : Nat) : Int) ∣ (a * b).coeff n := by
    rw [DensePoly.coeff_mul, DensePoly.mulCoeffSum]
    exact foldl_mulCoeffSum_dvd_mod_square_of_congr_zero
      m a b ha hb n (List.range a.size) 0 ⟨0, by simp⟩
  simpa using Int.emod_eq_zero_of_dvd hdvd

private theorem one_sub_square_congr_one_of_square_congr_zero
    (m : Nat) (b : ZPoly)
    (_hm : 1 < m)
    (hb2 : ZPoly.congr (b * b) 0 (m * m)) :
    ZPoly.congr (1 - b * b) 1 (m * m) := by
  intro i
  have hb2i : ((b * b).coeff i) % ((m * m : Nat) : Int) = 0 := by
    simpa using hb2 i
  have hdvd : ((m * m : Nat) : Int) ∣ (b * b).coeff i :=
    Int.dvd_of_emod_eq_zero hb2i
  have hneg : ((m * m : Nat) : Int) ∣ -((b * b).coeff i) :=
    Int.dvd_neg.mpr hdvd
  have hcoeff :
      ((1 - b * b : ZPoly).coeff i - (1 : ZPoly).coeff i) =
        -((b * b).coeff i) := by
    rw [DensePoly.coeff_sub]
    · omega
    · rfl
  rw [hcoeff]
  exact Int.emod_eq_zero_of_dvd hneg

private theorem quadraticHenselStep_bezout_error_congr_zero_core
    (m : Nat)
    (f g h s t : ZPoly)
    (hm : 1 < m)
    (hprod : ZPoly.congr (g * h) f m)
    (hbez : ZPoly.congr (s * g + t * h) 1 m)
    (hmonic : DensePoly.Monic g) :
    let e := QuadraticLiftResult.factorError f g h
    let te := mulModSquare t e m
    let factorQR := divModMonicModSquare te g m
    let qFactor := factorQR.1
    let rFactor := factorQR.2
    let g' := addModSquare g rFactor m
    let hCorrection := addModSquare (mulModSquare s e m) (mulModSquare qFactor h m) m
    let h' := addModSquare h hCorrection m
    let b := subModSquare (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m) 1 m
    ZPoly.congr b 0 m := by
  exact quadraticHenselStep_bezout_error_from_factor_update m f g h s t hm hprod hbez hmonic

private theorem mul_sub_right_exact
    (x y z : ZPoly) :
    x * z - y * z = (x - y) * z := by
  calc
    x * z - y * z
        = x * z + (0 - y * z) := by
          exact DensePoly.sub_eq_add_neg_poly (x * z) (y * z)
    _ = x * z + (0 - y) * z := by
          rw [DensePoly.neg_mul_right_poly y z]
    _ = (x + (0 - y)) * z := by
          exact (DensePoly.mul_add_left_poly x (0 - y) z).symm
    _ = (x - y) * z := by
          rw [DensePoly.sub_eq_add_neg_poly x y]

private theorem congr_mul_right_zero_mod_square
    (m : Nat) (x y z : ZPoly)
    (hxy : ZPoly.congr x y m)
    (hz : ZPoly.congr z 0 m) :
    ZPoly.congr (x * z) (y * z) (m * m) := by
  have hdiffBase : ZPoly.congr (x - y) 0 m := by
    have hsub : ZPoly.congr (x - y) (y - y) m :=
      congr_sub x y y y m hxy (ZPoly.congr_refl y m)
    simpa [sub_self_eq_zero y] using hsub
  have hmul :
      ZPoly.congr ((x - y) * z) 0 (m * m) :=
    mul_congr_zero_mod_square_of_congr_zero m (x - y) z hdiffBase hz
  intro i
  have hi : ((x * z - y * z).coeff i - (0 : ZPoly).coeff i) %
      (((m * m : Nat) : Int)) = 0 := by
    simpa [mul_sub_right_exact x y z] using hmul i
  rw [DensePoly.coeff_sub, DensePoly.coeff_zero] at hi
  · simpa [Int.sub_zero] using hi
  · rfl

private theorem quadraticHenselStep_factor_update_expand_exact
    (g h r c : ZPoly) :
    (g + r) * (h + c) = g * h + (g * c + r * h) + r * c := by
  calc
    (g + r) * (h + c)
        = (g + r) * h + (g + r) * c := by
          rw [DensePoly.mul_add_right_poly]
    _ = (g * h + r * h) + (g * c + r * c) := by
          rw [DensePoly.mul_add_left_poly, DensePoly.mul_add_left_poly]
    _ = g * h + (g * c + r * h) + r * c := by
          apply DensePoly.ext_coeff
          intro n
          repeat rw [DensePoly.coeff_add]
          all_goals try rfl
          omega

private theorem quadraticHenselStep_factor_first_order_exact
    (g h s e q r : ZPoly) :
    g * (s * e + q * h) + r * h =
      (s * g) * e + (q * g + r) * h := by
  calc
    g * (s * e + q * h) + r * h
        = (g * (s * e) + g * (q * h)) + r * h := by
          rw [DensePoly.mul_add_right_poly]
    _ = ((s * g) * e + (q * g) * h) + r * h := by
          rw [← DensePoly.mul_assoc_poly g s e, DensePoly.mul_comm_poly g s,
            ← DensePoly.mul_assoc_poly g q h, DensePoly.mul_comm_poly g q]
    _ = (s * g) * e + ((q * g) * h + r * h) := by
          apply DensePoly.ext_coeff
          intro n
          repeat rw [DensePoly.coeff_add]
          all_goals try rfl
          omega
    _ = (s * g) * e + (q * g + r) * h := by
          rw [DensePoly.mul_add_left_poly]

private theorem quadraticHenselStep_factor_first_order_bezout_exact
    (g h s t e : ZPoly) :
    (s * g) * e + (t * e) * h = (s * g + t * h) * e := by
  calc
    (s * g) * e + (t * e) * h
        = (s * g) * e + (t * h) * e := by
          rw [DensePoly.mul_assoc_poly t e h, DensePoly.mul_comm_poly e h,
            ← DensePoly.mul_assoc_poly t h e]
    _ = (s * g + t * h) * e := by
          rw [DensePoly.mul_add_left_poly]

private theorem quadraticHenselStep_factor_error_add_exact
    (f g h e : ZPoly)
    (he : e = QuadraticLiftResult.factorError f g h) :
    g * h + e = f := by
  rw [he, QuadraticLiftResult.factorError]
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_add, DensePoly.coeff_sub]
  · omega
  · rfl
  · rfl

/-- Word-sized quadratic Hensel doubling step over `WordMod` at working modulus
`m*m`, taken when `m*m` fits an odd machine word, `1 < m*m`, and the divisor `g`
is monic of positive degree. Byte-identical to `quadraticHenselStepBignum` under
that guard; declines (`none`) otherwise. -/
@[expose]
def quadraticHenselStepWord? (m : Nat) (f g h s t : ZPoly) : Option QuadraticLiftResult :=
  if _h2 : m * m < UInt64.word then
    if hodd : (UInt64.ofNat (m * m)) % 2 = 1 then
      if _h1 : 1 < m * m then
        if _hm : DensePoly.leadingCoeff g = 1 then
          if _hd : 0 < g.degree?.getD 0 then
            let ctx := _root_.MontCtx.mk (UInt64.ofNat (m * m)) hodd
            let eW := ZPoly.toWP ctx f - ZPoly.toWP ctx g * ZPoly.toWP ctx h
            let factorQR := DensePoly.divMod (ZPoly.toWP ctx t * eW) (ZPoly.toWP ctx g)
            let gW' := ZPoly.toWP ctx g + factorQR.2
            let hW' := ZPoly.toWP ctx h +
              (ZPoly.toWP ctx s * eW + factorQR.1 * ZPoly.toWP ctx h)
            let bW := (ZPoly.toWP ctx s * gW' + ZPoly.toWP ctx t * hW') - 1
            let bezoutQR := DensePoly.divMod (ZPoly.toWP ctx t * bW) gW'
            let tW' := ZPoly.toWP ctx t - bezoutQR.2
            let sW' := (ZPoly.toWP ctx s - ZPoly.toWP ctx s * bW) - bezoutQR.1 * hW'
            some { g := ZPoly.ofWP ctx gW', h := ZPoly.ofWP ctx hW',
                   s := ZPoly.ofWP ctx sW', t := ZPoly.ofWP ctx tW' }
          else none
        else none
      else none
    else none
  else none

/-- One quadratic Hensel correction step from modulus `m` to modulus `m^2`.

Inputs: the target polynomial `f`, the current monic factor `g`, the
complementary factor `h`, and the Bezout witnesses `s`, `t` for the current
factorisation. Preconditions consumed by the spec theorems below are `g`
monic, `g * h ≡ f (mod m)`, and `s * g + t * h ≡ 1 (mod m)`; the returned
`QuadraticLiftResult` then satisfies the same conjuncts modulo `m^2`. -/
def quadraticHenselStepBignum
    (m : Nat) (f g h s t : ZPoly) : QuadraticLiftResult :=
  let e := QuadraticLiftResult.factorError f g h
  let te := mulModSquare t e m
  let factorQR := divModMonicModSquare te g m
  let qFactor := factorQR.1
  let rFactor := factorQR.2
  let g' := addModSquare g rFactor m
  let hCorrection := addModSquare (mulModSquare s e m) (mulModSquare qFactor h m) m
  let h' := addModSquare h hCorrection m
  let b := subModSquare (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m) 1 m
  let tb := mulModSquare t b m
  let bezoutQR := divModMonicModSquare tb g' m
  let qBezout := bezoutQR.1
  let rBezout := bezoutQR.2
  let t' := subModSquare t rBezout m
  let s' := subModSquare (subModSquare s (mulModSquare s b m) m) (mulModSquare qBezout h' m) m
  { g := g', h := h', s := s', t := t' }

/-- Guarded dispatch: the word-sized step when its guard holds, else the bignum step. -/
def quadraticHenselStep
    (m : Nat) (f g h s t : ZPoly) : QuadraticLiftResult :=
  (quadraticHenselStepWord? m f g h s t).getD (quadraticHenselStepBignum m f g h s t)

set_option maxHeartbeats 2000000 in
private theorem quadraticHenselStep_raw_factor_congr
    (m : Nat)
    (f g h s t : ZPoly)
    (hm : 0 < m)
    (hprod : ZPoly.congr (g * h) f m)
    (hbez : ZPoly.congr (s * g + t * h) 1 m)
    (_hmonic : DensePoly.Monic g) :
    let e := QuadraticLiftResult.factorError f g h
    let te := mulModSquare t e m
    let factorQR := divModMonicModSquare te g m
    let qFactor := factorQR.1
    let rFactor := factorQR.2
    let g' := addModSquare g rFactor m
    let hCorrection := addModSquare (mulModSquare s e m) (mulModSquare qFactor h m) m
    let h' := addModSquare h hCorrection m
    ZPoly.congr (g' * h') f (m * m) := by
  intro e te factorQR qFactor rFactor g' hCorrection h'
  have heq : e = QuadraticLiftResult.factorError f g h := rfl
  have he : ZPoly.congr e 0 m := by
    have hf : ZPoly.congr f (g * h) m := ZPoly.congr_symm (g * h) f m hprod
    simpa [e, QuadraticLiftResult.factorError, sub_self_eq_zero (g * h)] using
      congr_sub f (g * h) (g * h) (g * h) m hf (ZPoly.congr_refl (g * h) m)
  have hteSq : ZPoly.congr te (t * e) (m * m) := by
    simpa [te] using mulModSquare_congr m t e hm
  have hteBase : ZPoly.congr te 0 m := by
    have htBase : ZPoly.congr (t * e) 0 m :=
      mul_right_zero_mod_base m t e he
    exact ZPoly.congr_trans te (t * e) 0 m
      (congr_of_square_mod m te (t * e) hteSq) htBase
  have hpair : (qFactor, rFactor) = divModMonicModSquare te g m := by
    simp [factorQR, qFactor, rFactor]
  have hqr : ZPoly.congr qFactor 0 m ∧ ZPoly.congr rFactor 0 m :=
    divModMonicModSquare_zero_mod_base m te g qFactor rFactor hteBase hpair
  have hdivMod :
      ZPoly.congr (qFactor * g + rFactor) te (m * m) :=
    divModMonicModSquare_reconstruct_congr m te g qFactor rFactor hm hpair
  have hdiv :
      ZPoly.congr (qFactor * g + rFactor) (t * e) (m * m) :=
    ZPoly.congr_trans _ _ _ (m * m) hdivMod hteSq
  let c := s * e + qFactor * h
  have hseBase : ZPoly.congr (s * e) 0 m :=
    mul_right_zero_mod_base m s e he
  have hqhBase : ZPoly.congr (qFactor * h) 0 m := by
    simpa [DensePoly.zero_mul] using
      ZPoly.congr_mul qFactor h 0 h m hqr.1 (ZPoly.congr_refl h m)
  have hcBase : ZPoly.congr c 0 m := by
    simpa [c, DensePoly.zero_add] using
      ZPoly.congr_add (s * e) (qFactor * h) 0 0 m hseBase hqhBase
  have hseSq :
      ZPoly.congr (mulModSquare s e m) (s * e) (m * m) :=
    mulModSquare_congr m s e hm
  have hqhSq :
      ZPoly.congr (mulModSquare qFactor h m) (qFactor * h) (m * m) :=
    mulModSquare_congr m qFactor h hm
  have hCorrectionSq : ZPoly.congr hCorrection c (m * m) := by
    have haddRed :
        ZPoly.congr hCorrection
          (mulModSquare s e m + mulModSquare qFactor h m) (m * m) := by
      simpa [hCorrection] using
        addModSquare_congr m (mulModSquare s e m) (mulModSquare qFactor h m) hm
    have haddPlain :
        ZPoly.congr
          (mulModSquare s e m + mulModSquare qFactor h m)
          c
          (m * m) := by
      simpa [c] using
        ZPoly.congr_add (mulModSquare s e m) (mulModSquare qFactor h m)
          (s * e) (qFactor * h) (m * m) hseSq hqhSq
    exact ZPoly.congr_trans _ _ _ (m * m) haddRed haddPlain
  have hg'Sq : ZPoly.congr g' (g + rFactor) (m * m) := by
    simpa [g'] using addModSquare_congr m g rFactor hm
  have hh'Sq : ZPoly.congr h' (h + c) (m * m) := by
    have haddRed : ZPoly.congr h' (h + hCorrection) (m * m) := by
      simpa [h'] using addModSquare_congr m h hCorrection hm
    have haddPlain : ZPoly.congr (h + hCorrection) (h + c) (m * m) :=
      ZPoly.congr_add h hCorrection h c (m * m) (ZPoly.congr_refl h (m * m)) hCorrectionSq
    exact ZPoly.congr_trans _ _ _ (m * m) haddRed haddPlain
  have hprodExpanded :
      ZPoly.congr (g' * h') ((g + rFactor) * (h + c)) (m * m) :=
    ZPoly.congr_mul g' h' (g + rFactor) (h + c) (m * m) hg'Sq hh'Sq
  have hcross :
      ZPoly.congr (rFactor * c) 0 (m * m) :=
    mul_congr_zero_mod_square_of_congr_zero m rFactor c hqr.2 hcBase
  have hfirstExact :
      g * c + rFactor * h =
        (s * g) * e + (qFactor * g + rFactor) * h := by
    simpa [c] using
      quadraticHenselStep_factor_first_order_exact g h s e qFactor rFactor
  have hdivH :
      ZPoly.congr ((qFactor * g + rFactor) * h) ((t * e) * h) (m * m) :=
    ZPoly.congr_mul (qFactor * g + rFactor) h (t * e) h
      (m * m) hdiv (ZPoly.congr_refl h (m * m))
  have hfirstToBez :
      ZPoly.congr (g * c + rFactor * h) ((s * g + t * h) * e) (m * m) := by
    have hstep :
        ZPoly.congr
          ((s * g) * e + (qFactor * g + rFactor) * h)
          ((s * g) * e + (t * e) * h)
          (m * m) :=
      ZPoly.congr_add ((s * g) * e) ((qFactor * g + rFactor) * h)
        ((s * g) * e) ((t * e) * h) (m * m)
        (ZPoly.congr_refl ((s * g) * e) (m * m)) hdivH
    exact ZPoly.congr_trans _ _ _ (m * m)
      (by simpa [hfirstExact] using ZPoly.congr_refl (g * c + rFactor * h) (m * m))
      (ZPoly.congr_trans _ _ _ (m * m) hstep
        (by
          simpa [quadraticHenselStep_factor_first_order_bezout_exact g h s t e] using
            ZPoly.congr_refl ((s * g) * e + (t * e) * h) (m * m)))
  have hbezE :
      ZPoly.congr ((s * g + t * h) * e) (1 * e) (m * m) :=
    congr_mul_right_zero_mod_square m (s * g + t * h) 1 e hbez he
  have honeE : (1 : ZPoly) * e = e := by
    rw [DensePoly.mul_comm_poly (1 : ZPoly) e]
    exact DensePoly.mul_one_right_poly e
  have hOneE : ZPoly.congr ((1 : ZPoly) * e) e (m * m) := by
    rw [honeE]
    exact ZPoly.congr_refl e (m * m)
  have hfirst :
      ZPoly.congr (g * c + rFactor * h) e (m * m) :=
    ZPoly.congr_trans _ _ _ (m * m) hfirstToBez
      (ZPoly.congr_trans _ _ _ (m * m) hbezE hOneE)
  have hexpandedToError :
      ZPoly.congr ((g + rFactor) * (h + c)) (g * h + e) (m * m) := by
    have hexpand :
        (g + rFactor) * (h + c) =
          g * h + (g * c + rFactor * h) + rFactor * c :=
      quadraticHenselStep_factor_update_expand_exact g h rFactor c
    rw [hexpand]
    have hsum :
        ZPoly.congr (g * h + (g * c + rFactor * h) + rFactor * c)
          (g * h + e + 0) (m * m) :=
      ZPoly.congr_add (g * h + (g * c + rFactor * h)) (rFactor * c)
        (g * h + e) 0 (m * m)
        (ZPoly.congr_add (g * h) (g * c + rFactor * h) (g * h) e
          (m * m) (ZPoly.congr_refl (g * h) (m * m)) hfirst)
        hcross
    have hzero : g * h + e + (0 : ZPoly) = g * h + e := by
      apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_add, DensePoly.coeff_zero]
      · omega
      · rfl
    exact ZPoly.congr_trans _ _ _ (m * m) hsum
      (by simpa [hzero] using ZPoly.congr_refl (g * h + e + (0 : ZPoly)) (m * m))
  have herror : g * h + e = f :=
    quadraticHenselStep_factor_error_add_exact f g h e heq
  exact ZPoly.congr_trans _ _ _ (m * m) hprodExpanded
    (by simpa [herror] using hexpandedToError)

private theorem quadraticHenselStep_bezout_error_congr_zero
    (m : Nat)
    (f g h s t : ZPoly)
    (hm : 1 < m)
    (hprod : ZPoly.congr (g * h) f m)
    (hbez : ZPoly.congr (s * g + t * h) 1 m)
    (hmonic : DensePoly.Monic g) :
    let e := QuadraticLiftResult.factorError f g h
    let te := mulModSquare t e m
    let factorQR := divModMonicModSquare te g m
    let qFactor := factorQR.1
    let rFactor := factorQR.2
    let g' := addModSquare g rFactor m
    let hCorrection := addModSquare (mulModSquare s e m) (mulModSquare qFactor h m) m
    let h' := addModSquare h hCorrection m
    let b := subModSquare (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m) 1 m
    ZPoly.congr b 0 m := by
  exact quadraticHenselStep_bezout_error_congr_zero_core m f g h s t hm hprod hbez hmonic

private theorem quadraticHenselStep_bezout_correction_congr
    (m : Nat)
    (f g h s t : ZPoly)
    (hm : 1 < m)
    (_hprod : ZPoly.congr (g * h) f m)
    (_hbez : ZPoly.congr (s * g + t * h) 1 m)
    (_hmonic : DensePoly.Monic g) :
    let e := QuadraticLiftResult.factorError f g h
    let te := mulModSquare t e m
    let factorQR := divModMonicModSquare te g m
    let qFactor := factorQR.1
    let rFactor := factorQR.2
    let g' := addModSquare g rFactor m
    let hCorrection := addModSquare (mulModSquare s e m) (mulModSquare qFactor h m) m
    let h' := addModSquare h hCorrection m
    let b := subModSquare (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m) 1 m
    let tb := mulModSquare t b m
    let bezoutQR := divModMonicModSquare tb g' m
    let qBezout := bezoutQR.1
    let rBezout := bezoutQR.2
    let t' := subModSquare t rBezout m
    let s' := subModSquare (subModSquare s (mulModSquare s b m) m) (mulModSquare qBezout h' m) m
    ZPoly.congr (s' * g' + t' * h') (1 - b * b) (m * m) := by
  intro e te factorQR qFactor rFactor g' hCorrection h' b tb bezoutQR qBezout rBezout t' s'
  have hbezoutQR :
      (let tb := mulModSquare t b m
       let bezoutQR := divModMonicModSquare tb g' m
       qBezout = bezoutQR.1 ∧ rBezout = bezoutQR.2) := by
    simp [tb, bezoutQR, qBezout, rBezout]
  have hb :
      ZPoly.congr b (s * g' + t * h' - 1) (m * m) :=
    quadraticHenselStep_bezout_error_definition_congr m s t g' h' b
      (Nat.lt_trans Nat.zero_lt_one hm)
      (by simp [b])
  simpa [t', s'] using
    quadraticHenselStep_bezout_correction_congr_core
      m g' h' s t b qBezout rBezout hm hb hbezoutQR

private theorem congr_one_sub_square_of_congr_zero
    (m : Nat) (b : ZPoly)
    (hm : 1 < m)
    (hb : ZPoly.congr b 0 m) :
    ZPoly.congr (1 - b * b) 1 (m * m) := by
  exact one_sub_square_congr_one_of_square_congr_zero m b hm
    (square_congr_zero_mod_square m b hm hb)

private theorem quadraticHenselStep_raw_bezout_congr
    (m : Nat)
    (f g h s t : ZPoly)
    (hm : 1 < m)
    (hprod : ZPoly.congr (g * h) f m)
    (hbez : ZPoly.congr (s * g + t * h) 1 m)
    (hmonic : DensePoly.Monic g) :
    let e := QuadraticLiftResult.factorError f g h
    let te := mulModSquare t e m
    let factorQR := divModMonicModSquare te g m
    let qFactor := factorQR.1
    let rFactor := factorQR.2
    let g' := addModSquare g rFactor m
    let hCorrection := addModSquare (mulModSquare s e m) (mulModSquare qFactor h m) m
    let h' := addModSquare h hCorrection m
    let b := subModSquare (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m) 1 m
    let tb := mulModSquare t b m
    let bezoutQR := divModMonicModSquare tb g' m
    let qBezout := bezoutQR.1
    let rBezout := bezoutQR.2
    let t' := subModSquare t rBezout m
    let s' := subModSquare (subModSquare s (mulModSquare s b m) m) (mulModSquare qBezout h' m) m
    ZPoly.congr (s' * g' + t' * h') 1 (m * m) := by
  intro e te factorQR qFactor rFactor g' hCorrection h' b tb bezoutQR qBezout rBezout t' s'
  have hb : ZPoly.congr b 0 m := by
    simpa [e, te, factorQR, qFactor, rFactor, g', hCorrection, h'] using
      quadraticHenselStep_bezout_error_congr_zero m f g h s t hm hprod hbez hmonic
  exact ZPoly.congr_trans
    (s' * g' + t' * h')
    (1 - b * b)
    1
    (m * m)
    (by
      simpa [e, te, factorQR, qFactor, rFactor, g', hCorrection, h', b, tb,
        bezoutQR, qBezout, rBezout, t', s'] using
        quadraticHenselStep_bezout_correction_congr m f g h s t hm hprod hbez hmonic)
    (congr_one_sub_square_of_congr_zero m b hm hb)

private theorem divModMonicModSquare_remainder_coeff_eq_zero_of_monic
    (m : Nat)
    (p g : ZPoly)
    (_hm : 1 < m)
    (_hmonic : DensePoly.Monic g) :
    let qr := divModMonicModSquare p g m
    ∀ i, g.size - 1 ≤ i → qr.2.coeff i = 0 := by
  unfold divModMonicModSquare
  let pRed := QuadraticLiftResult.reduceModSquare p m
  exact
    divModMonicModSquareAux_remainder_coeff_eq_zero_of_monic
      m g pRed.size 0 pRed
      (divModMonicModSquareAux m g pRed.size 0 pRed).1
      (divModMonicModSquareAux m g pRed.size 0 pRed).2
      _hm _hmonic (by omega) rfl

private theorem addModSquare_monic_of_high_remainder_zero
    (m : Nat)
    (g r : ZPoly)
    (_hm : 1 < m)
    (hmonic : DensePoly.Monic g)
    (hr : ∀ i, g.size - 1 ≤ i → r.coeff i = 0) :
    DensePoly.Monic (addModSquare g r m) := by
  have hgpos : 0 < g.size := by
    by_cases hpos : 0 < g.size
    · exact hpos
    · have hsize : g.size = 0 := Nat.eq_zero_of_not_pos hpos
      have hlead : g.leadingCoeff = 0 := by
        cases g with
        | mk coeffs normalized =>
            simp only [DensePoly.leadingCoeff, DensePoly.size] at hsize ⊢
            simp [hsize, Array.getD] <;> rfl
      have hmonicLead : g.leadingCoeff = 1 :=
        DensePoly.leadingCoeff_eq_one_of_monic hmonic
      rw [hlead] at hmonicLead
      exact False.elim (Int.zero_ne_one hmonicLead)
  apply monic_of_coeff_eq_one_and_high_coeff_zero
      (QuadraticLiftResult.reduceModSquare (g + r) m) (g.size - 1)
  · unfold QuadraticLiftResult.reduceModSquare
    rw [ZPoly.coeff_reduceModPow]
    have hg : g.coeff (g.size - 1) = 1 := by
      rw [coeff_last_eq_leadingCoeff g hgpos]
      exact hmonic
    have hr' : r.coeff (g.size - 1) = 0 := hr (g.size - 1) (by omega)
    rw [DensePoly.coeff_add]
    · rw [hg, hr']
      change Int.ofNat (Int.toNat ((1 : Int) % Int.ofNat (m ^ 2))) = 1
      have hmsq_gt_one : 1 < m ^ 2 := by
        calc
          1 < 2 ^ 2 := by decide
          _ ≤ m ^ 2 := Nat.pow_le_pow_left _hm 2
      have hlt : (1 : Int) < Int.ofNat (m ^ 2) := by
        simpa using (Int.ofNat_lt.mpr hmsq_gt_one)
      rw [Int.emod_eq_of_lt (by decide : (0 : Int) ≤ 1) hlt]
      rfl
    · rfl
  · intro i hi
    unfold QuadraticLiftResult.reduceModSquare
    rw [ZPoly.coeff_reduceModPow]
    have hg : g.coeff i = 0 := by
      exact DensePoly.coeff_eq_zero_of_size_le g (by omega)
    have hr' : r.coeff i = 0 := hr i (by omega)
    rw [DensePoly.coeff_add]
    · rw [hg, hr']
      change Int.ofNat (Int.toNat ((0 : Int) % Int.ofNat (m ^ 2))) = 0
      simp
    · rfl

private theorem addModSquare_divModMonicModSquare_remainder_monic
    (m : Nat)
    (p g : ZPoly)
    (hm : 1 < m)
    (hmonic : DensePoly.Monic g) :
    let qr := divModMonicModSquare p g m
    DensePoly.Monic (addModSquare g qr.2 m) := by
  let qr := divModMonicModSquare p g m
  have hr : ∀ i, g.size - 1 ≤ i → qr.2.coeff i = 0 := by
    simpa [qr] using
      divModMonicModSquare_remainder_coeff_eq_zero_of_monic m p g hm hmonic
  exact addModSquare_monic_of_high_remainder_zero m g qr.2 hm hmonic hr

private theorem quadraticHenselStep_g_update_monic
    (m : Nat)
    (f g h _s t : ZPoly)
    (hm : 1 < m)
    (hmonic : DensePoly.Monic g) :
    let e := QuadraticLiftResult.factorError f g h
    let te := mulModSquare t e m
    let factorQR := divModMonicModSquare te g m
    let rFactor := factorQR.2
    DensePoly.Monic (addModSquare g rFactor m) := by
  intro e te factorQR rFactor
  have hmono :
      (let qr := divModMonicModSquare te g m
       DensePoly.Monic (addModSquare g qr.2 m)) :=
    addModSquare_divModMonicModSquare_remainder_monic m te g hm hmonic
  simpa [factorQR, rFactor] using hmono

/-! ### Word transport of the mod-`m²` primitives and the byte-identity proof -/

private theorem QuadraticLiftResult.ext' {r1 r2 : QuadraticLiftResult}
    (hg : r1.g = r2.g) (hh : r1.h = r2.h) (hs : r1.s = r2.s) (ht : r1.t = r2.t) :
    r1 = r2 := by
  cases r1
  cases r2
  simp_all

private theorem toWP_reduceModSquare (m : Nat) (ctx : _root_.MontCtx (UInt64.ofNat (m * m)))
    (hM : (UInt64.ofNat (m * m)).toNat = m * m) (hm0 : 0 < m * m) (x : ZPoly) :
    ZPoly.toWP ctx (QuadraticLiftResult.reduceModSquare x m) = ZPoly.toWP ctx x := by
  unfold QuadraticLiftResult.reduceModSquare
  exact ZPoly.toWP_reduceModPow ctx (by rw [hM, Nat.pow_two])
    (by rw [Nat.pow_two]; exact hm0) x

private theorem toWP_addModSquare (m : Nat) (ctx : _root_.MontCtx (UInt64.ofNat (m * m)))
    (hM : (UInt64.ofNat (m * m)).toNat = m * m) (hm0 : 0 < m * m) (a b : ZPoly) :
    ZPoly.toWP ctx (addModSquare a b m) = ZPoly.toWP ctx a + ZPoly.toWP ctx b := by
  unfold addModSquare
  rw [toWP_reduceModSquare m ctx hM hm0, ZPoly.toWP_add]

private theorem toWP_subModSquare (m : Nat) (ctx : _root_.MontCtx (UInt64.ofNat (m * m)))
    (hM : (UInt64.ofNat (m * m)).toNat = m * m) (hm0 : 0 < m * m) (a b : ZPoly) :
    ZPoly.toWP ctx (subModSquare a b m) = ZPoly.toWP ctx a - ZPoly.toWP ctx b := by
  unfold subModSquare
  rw [toWP_reduceModSquare m ctx hM hm0, ZPoly.toWP_sub]

private theorem toWP_mulModSquare (m : Nat) (ctx : _root_.MontCtx (UInt64.ofNat (m * m)))
    (hM : (UInt64.ofNat (m * m)).toNat = m * m) (hm0 : 0 < m * m) (a b : ZPoly) :
    ZPoly.toWP ctx (mulModSquare a b m) = ZPoly.toWP ctx a * ZPoly.toWP ctx b := by
  unfold mulModSquare
  rw [toWP_reduceModSquare m ctx hM hm0, ZPoly.toWP_mul]

private theorem reduceModSquare_coeff_lt (m : Nat) (hm0 : 0 < m * m) (x : ZPoly) (i : Nat) :
    0 ≤ (QuadraticLiftResult.reduceModSquare x m).coeff i ∧
      (QuadraticLiftResult.reduceModSquare x m).coeff i < (m * m : Int) := by
  unfold QuadraticLiftResult.reduceModSquare
  rw [ZPoly.coeff_reduceModPow, Int.ofNat_eq_natCast]
  refine ⟨Int.natCast_nonneg _, ?_⟩
  have hlt := ZPoly.intModNat_lt' (x.coeff i) (M := m ^ 2)
    (by rw [Nat.pow_two]; exact hm0)
  rw [show (m * m : Int) = ((m ^ 2 : Nat) : Int) from by
    rw [Nat.pow_two]
    exact_mod_cast rfl]
  exact_mod_cast hlt

private theorem ofWP_toWP_reduceModSquare (m : Nat)
    (ctx : _root_.MontCtx (UInt64.ofNat (m * m)))
    (hM : (UInt64.ofNat (m * m)).toNat = m * m) (hm0 : 0 < m * m) (x : ZPoly) :
    ZPoly.ofWP ctx (ZPoly.toWP ctx (QuadraticLiftResult.reduceModSquare x m)) =
      QuadraticLiftResult.reduceModSquare x m := by
  apply ZPoly.ofWP_toWP_of_canonical
  intro i
  refine ⟨(reduceModSquare_coeff_lt m hm0 x i).1, ?_⟩
  rw [show ((UInt64.ofNat (m * m)).toNat : Int) = (m * m : Int) from by
    rw [hM]
    exact_mod_cast rfl]
  exact (reduceModSquare_coeff_lt m hm0 x i).2

private theorem ofWP_toWP_addModSquare (m : Nat)
    (ctx : _root_.MontCtx (UInt64.ofNat (m * m)))
    (hM : (UInt64.ofNat (m * m)).toNat = m * m) (hm0 : 0 < m * m) (a b : ZPoly) :
    ZPoly.ofWP ctx (ZPoly.toWP ctx (addModSquare a b m)) = addModSquare a b m := by
  unfold addModSquare
  exact ofWP_toWP_reduceModSquare m ctx hM hm0 (a + b)

private theorem ofWP_toWP_subModSquare (m : Nat)
    (ctx : _root_.MontCtx (UInt64.ofNat (m * m)))
    (hM : (UInt64.ofNat (m * m)).toNat = m * m) (hm0 : 0 < m * m) (a b : ZPoly) :
    ZPoly.ofWP ctx (ZPoly.toWP ctx (subModSquare a b m)) = subModSquare a b m := by
  unfold subModSquare
  exact ofWP_toWP_reduceModSquare m ctx hM hm0 (a - b)

private theorem one_lt_of_mul (m : Nat) (h1 : 1 < m * m) : 1 < m := by
  rcases m with _ | _ | k
  · simp at h1
  · simp at h1
  · omega

/-- Transport of the custom monic modular division through `toWP`. -/
private theorem toWP_divModMonicModSquare (m : Nat)
    (ctx : _root_.MontCtx (UInt64.ofNat (m * m)))
    (hM : (UInt64.ofNat (m * m)).toNat = m * m) (hm1 : 1 < m * m)
    (p q : ZPoly) (hqm : DensePoly.Monic q) (hqd : 0 < q.degree?.getD 0) :
    DensePoly.divMod (ZPoly.toWP ctx p) (ZPoly.toWP ctx q) =
      (ZPoly.toWP ctx (divModMonicModSquare p q m).1,
       ZPoly.toWP ctx (divModMonicModSquare p q m).2) := by
  have hqpos : 0 < q.size := by
    rcases Nat.eq_zero_or_pos q.size with h0 | h0
    · exfalso
      rw [DensePoly.degree?, dif_pos h0] at hqd
      simp at hqd
    · exact h0
  have hm1' : 1 < (UInt64.ofNat (m * m)).toNat := by
    rw [hM]
    exact hm1
  have hmbase : 1 < m := one_lt_of_mul m hm1
  have hlc : (ZPoly.toWP ctx q).leadingCoeff = 1 :=
    ZPoly.toWP_monic ctx hqm hqpos hm1'
  refine DensePoly.divMod_eq_of_reconstruction (ZPoly.toWP ctx p) (ZPoly.toWP ctx q)
    (ZPoly.toWP ctx (divModMonicModSquare p q m).1)
    (ZPoly.toWP ctx (divModMonicModSquare p q m).2) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [ZPoly.toWP_degree_eq_of_monic ctx hqm hqpos hm1']
    exact hqd
  · intro a
    rw [hlc, WordMod.div_one, Lean.Grind.Semiring.mul_one]
    exact WordMod.sub_self a
  · intro a
    rw [hlc, WordMod.div_one, Lean.Grind.Semiring.mul_one]
  · intro a ha
    simpa [hlc, Lean.Grind.Semiring.mul_one] using ha
  · rw [← ZPoly.toWP_mul, ← ZPoly.toWP_add]
    exact ZPoly.toWP_congr ctx (by
      rw [hM]
      exact divModMonicModSquare_reconstruct_congr m p q _ _ (by omega) rfl)
  · rw [ZPoly.toWP_degree_eq_of_monic ctx hqm hqpos hm1']
    have hq2 : 2 ≤ q.size := by
      have hh := hqd
      rw [DensePoly.degree?_eq_some_of_pos_size q hqpos, Option.getD_some] at hh
      omega
    refine Nat.lt_of_le_of_lt (ZPoly.toWP_degree_le ctx (divModMonicModSquare p q m).2) ?_
    have hz := divModMonicModSquare_remainder_coeff_eq_zero_of_monic m p q hmbase hqm
    have hrsize : (divModMonicModSquare p q m).2.size ≤ q.size - 1 := by
      rcases Nat.lt_or_ge (q.size - 1) (divModMonicModSquare p q m).2.size with hlt | hge
      · exact absurd (hz _ (by omega))
          (DensePoly.coeff_last_ne_zero_of_pos_size _ (by omega))
      · exact hge
    rcases Nat.eq_zero_or_pos (divModMonicModSquare p q m).2.size with h0 | h0
    · rw [DensePoly.degree?, dif_pos h0, Option.getD_none,
        DensePoly.degree?_eq_some_of_pos_size q hqpos, Option.getD_some]
      omega
    · rw [DensePoly.degree?_eq_some_of_pos_size _ h0,
        DensePoly.degree?_eq_some_of_pos_size q hqpos, Option.getD_some, Option.getD_some]
      omega

set_option maxHeartbeats 1000000 in
theorem quadraticHenselStepWord?_eq (m : Nat) (f g h s t : ZPoly)
    (h2 : m * m < UInt64.word) (hodd : (UInt64.ofNat (m * m)) % 2 = 1) (h1 : 1 < m * m)
    (hmlc : DensePoly.leadingCoeff g = 1) (hd : 0 < g.degree?.getD 0) :
    quadraticHenselStepWord? m f g h s t = some (quadraticHenselStepBignum m f g h s t) := by
  have hM : (UInt64.ofNat (m * m)).toNat = m * m := by
    rw [UInt64.toNat_ofNat_mod_word]
    exact Nat.mod_eq_of_lt h2
  have hm0 : 0 < m * m := by omega
  have hgm : DensePoly.Monic g := hmlc
  have hgpos : 0 < g.size := by
    rcases Nat.eq_zero_or_pos g.size with h0 | h0
    · exfalso
      rw [DensePoly.degree?, dif_pos h0] at hd
      simp at hd
    · exact h0
  have hg2 : 2 ≤ g.size := by
    have hh := hd
    rw [DensePoly.degree?_eq_some_of_pos_size g hgpos, Option.getD_some] at hh
    omega
  have hmbase : 1 < m := one_lt_of_mul m h1
  unfold quadraticHenselStepWord?
  simp only [dif_pos h2, dif_pos hodd, dif_pos h1, dif_pos hmlc, dif_pos hd]
  generalize hctx : _root_.MontCtx.mk (UInt64.ofNat (m * m)) hodd = ctx
  refine congrArg some ?_
  generalize heW : ZPoly.toWP ctx f - ZPoly.toWP ctx g * ZPoly.toWP ctx h = eW
  generalize hfqW : DensePoly.divMod (ZPoly.toWP ctx t * eW) (ZPoly.toWP ctx g) = fqW
  generalize hgWv : ZPoly.toWP ctx g + fqW.2 = gWv
  generalize hhWv : ZPoly.toWP ctx h +
    (ZPoly.toWP ctx s * eW + fqW.1 * ZPoly.toWP ctx h) = hWv
  generalize hbWv : (ZPoly.toWP ctx s * gWv + ZPoly.toWP ctx t * hWv) - 1 = bWv
  generalize hbqW : DensePoly.divMod (ZPoly.toWP ctx t * bWv) gWv = bqW
  generalize htWv : ZPoly.toWP ctx t - bqW.2 = tWv
  generalize hsWv :
    (ZPoly.toWP ctx s - ZPoly.toWP ctx s * bWv) - bqW.1 * hWv = sWv
  obtain ⟨e, he⟩ : ∃ e, e = QuadraticLiftResult.factorError f g h := ⟨_, rfl⟩
  obtain ⟨fq, hfq⟩ : ∃ fq, fq = divModMonicModSquare (mulModSquare t e m) g m := ⟨_, rfl⟩
  obtain ⟨g', hg'⟩ : ∃ g', g' = addModSquare g fq.2 m := ⟨_, rfl⟩
  obtain ⟨hCorr, hhc⟩ : ∃ hCorr,
      hCorr = addModSquare (mulModSquare s e m) (mulModSquare fq.1 h m) m := ⟨_, rfl⟩
  obtain ⟨h', hh'⟩ : ∃ h', h' = addModSquare h hCorr m := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b,
      b = subModSquare (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m) 1 m :=
    ⟨_, rfl⟩
  obtain ⟨bq, hbq⟩ : ∃ bq, bq = divModMonicModSquare (mulModSquare t b m) g' m := ⟨_, rfl⟩
  have hEwe : eW = ZPoly.toWP ctx e := by
    rw [← heW, he]
    unfold QuadraticLiftResult.factorError
    rw [ZPoly.toWP_sub, ZPoly.toWP_mul]
  have hFqe : fqW = (ZPoly.toWP ctx fq.1, ZPoly.toWP ctx fq.2) := by
    rw [← hfqW, hEwe, ← toWP_mulModSquare m ctx hM hm0, hfq]
    exact toWP_divModMonicModSquare m ctx hM h1 _ g hgm hd
  have hg'monic0 : DensePoly.Monic (addModSquare g fq.2 m) := by
    rw [hfq]
    exact addModSquare_divModMonicModSquare_remainder_monic m _ g hmbase hgm
  have hg'monic : DensePoly.Monic g' :=
    (congrArg DensePoly.Monic hg').mpr hg'monic0
  have hg'coeff : g'.coeff (g.size - 1) = 1 := by
    rw [hg']
    unfold addModSquare QuadraticLiftResult.reduceModSquare
    rw [ZPoly.coeff_reduceModPow, DensePoly.coeff_add _ _ _ (by rfl),
      show g.coeff (g.size - 1) = 1 from by
        rw [← DensePoly.leadingCoeff_eq_coeff_last g hgpos]
        exact hgm,
      show fq.2.coeff (g.size - 1) = 0 from
        by
          rw [hfq]
          exact divModMonicModSquare_remainder_coeff_eq_zero_of_monic m _ g hmbase hgm
            (g.size - 1) (Nat.le_refl _),
      show (1 : Int) + 0 = 1 from by omega,
      ZPoly.intModNat_one (show 0 < m ^ 2 from by rw [Nat.pow_two]; exact hm0),
      Nat.mod_eq_of_lt (show 1 < m ^ 2 from by rw [Nat.pow_two]; exact h1)]
    rfl
  have hg'deg : 0 < g'.degree?.getD 0 := by
    have hg'size : g.size ≤ g'.size := by
      rcases Nat.lt_or_ge g'.size g.size with hlt | hge
      · exact absurd hg'coeff (by
          rw [DensePoly.coeff_eq_zero_of_size_le _ (by omega)]
          exact Int.zero_ne_one)
      · exact hge
    rw [DensePoly.degree?_eq_some_of_pos_size _ (by omega), Option.getD_some]
    omega
  have hGwe : gWv = ZPoly.toWP ctx g' := by
    rw [← hgWv, hFqe, hg', toWP_addModSquare m ctx hM hm0]
  have hHwe : hWv = ZPoly.toWP ctx h' := by
    rw [← hhWv, hEwe, hFqe, hh', toWP_addModSquare m ctx hM hm0, hhc,
      toWP_addModSquare m ctx hM hm0, toWP_mulModSquare m ctx hM hm0,
      toWP_mulModSquare m ctx hM hm0]
  have hBwe : bWv = ZPoly.toWP ctx b := by
    rw [← hbWv, hGwe, hHwe, hb, toWP_subModSquare m ctx hM hm0,
      toWP_addModSquare m ctx hM hm0, toWP_mulModSquare m ctx hM hm0,
      toWP_mulModSquare m ctx hM hm0, ZPoly.toWP_one]
  have hBqe : bqW = (ZPoly.toWP ctx bq.1, ZPoly.toWP ctx bq.2) := by
    rw [← hbqW, hBwe, hGwe, ← toWP_mulModSquare m ctx hM hm0, hbq]
    exact toWP_divModMonicModSquare m ctx hM h1 _ g' hg'monic hg'deg
  have hTwe : tWv = ZPoly.toWP ctx (subModSquare t bq.2 m) := by
    rw [← htWv, hBqe, toWP_subModSquare m ctx hM hm0]
  have hSwe : sWv = ZPoly.toWP ctx
      (subModSquare (subModSquare s (mulModSquare s b m) m)
        (mulModSquare bq.1 h' m) m) := by
    rw [← hsWv, hBwe, hBqe, hHwe, toWP_subModSquare m ctx hM hm0,
      toWP_subModSquare m ctx hM hm0, toWP_mulModSquare m ctx hM hm0,
      toWP_mulModSquare m ctx hM hm0]
  rw [hGwe, hHwe, hTwe, hSwe]
  refine QuadraticLiftResult.ext' ?_ ?_ ?_ ?_
  · calc
      ZPoly.ofWP ctx (ZPoly.toWP ctx g') = g' := by
        rw [hg']
        exact ofWP_toWP_addModSquare m ctx hM hm0 g fq.2
      _ = (quadraticHenselStepBignum m f g h s t).g := by
        unfold quadraticHenselStepBignum
        rw [hg', hfq, he]
  · calc
      ZPoly.ofWP ctx (ZPoly.toWP ctx h') = h' := by
        rw [hh']
        exact ofWP_toWP_addModSquare m ctx hM hm0 h hCorr
      _ = (quadraticHenselStepBignum m f g h s t).h := by
        unfold quadraticHenselStepBignum
        rw [hh', hhc, hfq, he]
  · calc
      ZPoly.ofWP ctx (ZPoly.toWP ctx
          (subModSquare (subModSquare s (mulModSquare s b m) m)
            (mulModSquare bq.1 h' m) m)) =
          subModSquare (subModSquare s (mulModSquare s b m) m)
            (mulModSquare bq.1 h' m) m :=
        ofWP_toWP_subModSquare m ctx hM hm0 _ _
      _ = (quadraticHenselStepBignum m f g h s t).s := by
        unfold quadraticHenselStepBignum
        rw [hbq, hb, hh', hhc, hg', hfq, he]
  · calc
      ZPoly.ofWP ctx (ZPoly.toWP ctx (subModSquare t bq.2 m)) =
          subModSquare t bq.2 m := ofWP_toWP_subModSquare m ctx hM hm0 t bq.2
      _ = (quadraticHenselStepBignum m f g h s t).t := by
        unfold quadraticHenselStepBignum
        rw [hbq, hb, hh', hhc, hg', hfq, he]

theorem quadraticHenselStep_eq_bignum
    (m : Nat) (f g h s t : ZPoly) :
    quadraticHenselStep m f g h s t = quadraticHenselStepBignum m f g h s t := by
  unfold quadraticHenselStep
  by_cases hguard : (m * m < UInt64.word) ∧ ((UInt64.ofNat (m * m)) % 2 = 1) ∧
      (1 < m * m) ∧ (DensePoly.leadingCoeff g = 1) ∧ (0 < g.degree?.getD 0)
  · obtain ⟨h2, hodd, h1, hmlc, hd⟩ := hguard
    rw [quadraticHenselStepWord?_eq m f g h s t h2 hodd h1 hmlc hd, Option.getD_some]
  · have hnone : quadraticHenselStepWord? m f g h s t = none := by
      unfold quadraticHenselStepWord?
      by_cases a : m * m < UInt64.word
      · rw [dif_pos a]
        by_cases b : (UInt64.ofNat (m * m)) % 2 = 1
        · rw [dif_pos b]
          by_cases c : 1 < m * m
          · rw [dif_pos c]
            by_cases d : DensePoly.leadingCoeff g = 1
            · rw [dif_pos d]
              by_cases e : 0 < g.degree?.getD 0
              · exact absurd ⟨a, b, c, d, e⟩ hguard
              · rw [dif_neg e]
            · rw [dif_neg d]
          · rw [dif_neg c]
        · rw [dif_neg b]
      · rw [dif_neg a]
    rw [hnone, Option.getD_none]

/-- The updated factors multiply to `f` modulo `m^2`. -/
@[grind =>]
theorem quadraticHenselStep_factor_spec
    (m : Nat)
    (f g h s t : ZPoly)
    (hm : 0 < m)
    (hprod : ZPoly.congr (g * h) f m)
    (hbez : ZPoly.congr (s * g + t * h) 1 m)
    (hmonic : DensePoly.Monic g) :
    let r := quadraticHenselStep m f g h s t
    ZPoly.congr (r.g * r.h) f (m * m) := by
  rw [quadraticHenselStep_eq_bignum]
  unfold quadraticHenselStepBignum
  exact quadraticHenselStep_raw_factor_congr m f g h s t hm hprod hbez hmonic

/-- The updated Bezout witnesses certify coprimality modulo `m^2`. -/
@[grind =>]
theorem quadraticHenselStep_bezout_spec
    (m : Nat)
    (f g h s t : ZPoly)
    (hm : 1 < m)
    (hprod : ZPoly.congr (g * h) f m)
    (hbez : ZPoly.congr (s * g + t * h) 1 m)
    (hmonic : DensePoly.Monic g) :
    let r := quadraticHenselStep m f g h s t
    ZPoly.congr (r.s * r.g + r.t * r.h) 1 (m * m) := by
  rw [quadraticHenselStep_eq_bignum]
  unfold quadraticHenselStepBignum
  exact quadraticHenselStep_raw_bezout_congr m f g h s t hm hprod hbez hmonic

/-- The quadratic step lifts both factor and Bezout congruences to modulus `m^2`. -/
@[grind =>]
theorem quadraticHenselStep_spec
    (m : Nat)
    (f g h s t : ZPoly)
    (hm : 1 < m)
    (hprod : ZPoly.congr (g * h) f m)
    (hbez : ZPoly.congr (s * g + t * h) 1 m)
    (hmonic : DensePoly.Monic g) :
    let r := quadraticHenselStep m f g h s t
    ZPoly.congr (r.g * r.h) f (m * m) ∧
      ZPoly.congr (r.s * r.g + r.t * r.h) 1 (m * m) := by
  exact
    ⟨quadraticHenselStep_factor_spec m f g h s t (Nat.lt_trans Nat.zero_lt_one hm)
        hprod hbez hmonic,
      quadraticHenselStep_bezout_spec m f g h s t hm hprod hbez hmonic⟩

/-- The monic factor remains monic after the quadratic correction. -/
@[grind =>]
theorem quadraticHenselStep_monic
    (m : Nat)
    (f g h s t : ZPoly)
    (hm : 1 < m)
    (hmonic : DensePoly.Monic g) :
    DensePoly.Monic (quadraticHenselStep m f g h s t).g := by
  rw [quadraticHenselStep_eq_bignum]
  unfold quadraticHenselStepBignum
  exact quadraticHenselStep_g_update_monic m f g h s t hm hmonic

/--
After a quadratic Hensel step, both the updated leading factor `r.g` and the
updated complementary factor `r.h` are congruent to the corresponding input
factors modulo `m`. The quadratic correction only touches the data modulo
`m^2` beyond what is already determined modulo `m`, so the input
factorisation is preserved at the base modulus.
-/
@[grind =>]
theorem quadraticHenselStep_factor_congr_mod_base
    (m : Nat) (f g h s t : ZPoly)
    (hm : 1 < m)
    (hprod : ZPoly.congr (g * h) f m) :
    ZPoly.congr (quadraticHenselStep m f g h s t).g g m ∧
      ZPoly.congr (quadraticHenselStep m f g h s t).h h m := by
  rw [quadraticHenselStep_eq_bignum]
  unfold quadraticHenselStepBignum
  have hm0 : 0 < m := Nat.lt_trans Nat.zero_lt_one hm
  let e := QuadraticLiftResult.factorError f g h
  let te := mulModSquare t e m
  let factorQR := divModMonicModSquare te g m
  let qFactor := factorQR.1
  let rFactor := factorQR.2
  let g' := addModSquare g rFactor m
  let hCorrection := addModSquare (mulModSquare s e m) (mulModSquare qFactor h m) m
  let h' := addModSquare h hCorrection m
  have he : ZPoly.congr e 0 m := by
    have hf : ZPoly.congr f (g * h) m := ZPoly.congr_symm (g * h) f m hprod
    simpa [e, QuadraticLiftResult.factorError, sub_self_eq_zero (g * h)] using
      congr_sub f (g * h) (g * h) (g * h) m hf (ZPoly.congr_refl (g * h) m)
  have hte : ZPoly.congr te 0 m := by
    have hmul : ZPoly.congr (mulModSquare t e m) (t * e) (m * m) :=
      mulModSquare_congr m t e hm0
    have hmulBase : ZPoly.congr (t * e) 0 m :=
      mul_right_zero_mod_base m t e he
    exact ZPoly.congr_trans te (t * e) 0 m
      (congr_of_square_mod m te (t * e) (by simpa [te] using hmul)) hmulBase
  have hpair : (qFactor, rFactor) = divModMonicModSquare te g m := by
    simp [factorQR, qFactor, rFactor]
  have hqr : ZPoly.congr qFactor 0 m ∧ ZPoly.congr rFactor 0 m :=
    divModMonicModSquare_zero_mod_base m te g qFactor rFactor hte hpair
  have hzero_add (a : ZPoly) : a + (0 : ZPoly) = a := by
    apply DensePoly.ext_coeff
    intro i
    rw [DensePoly.coeff_add, DensePoly.coeff_zero]
    · omega
    · rfl
  have hg' : ZPoly.congr g' g m := by
    have hadd : ZPoly.congr (addModSquare g rFactor m) (g + rFactor) (m * m) :=
      addModSquare_congr m g rFactor hm0
    have hbase : ZPoly.congr (g + rFactor) (g + 0) m :=
      ZPoly.congr_add g rFactor g 0 m (ZPoly.congr_refl g m) hqr.2
    exact ZPoly.congr_trans g' (g + rFactor) g m
      (congr_of_square_mod m g' (g + rFactor) (by simpa [g'] using hadd))
      (by simpa [hzero_add] using hbase)
  have hCorrection_zero : ZPoly.congr hCorrection 0 m := by
    have hseSq : ZPoly.congr (mulModSquare s e m) (s * e) (m * m) :=
      mulModSquare_congr m s e hm0
    have hse : ZPoly.congr (mulModSquare s e m) 0 m := by
      have hmulBase : ZPoly.congr (s * e) 0 m :=
        mul_right_zero_mod_base m s e he
      exact ZPoly.congr_trans (mulModSquare s e m) (s * e) 0 m
        (congr_of_square_mod m (mulModSquare s e m) (s * e) hseSq) hmulBase
    have hqhSq : ZPoly.congr (mulModSquare qFactor h m) (qFactor * h) (m * m) :=
      mulModSquare_congr m qFactor h hm0
    have hqh : ZPoly.congr (mulModSquare qFactor h m) 0 m := by
      have hmulBase : ZPoly.congr (qFactor * h) 0 m := by
        simpa [DensePoly.zero_mul] using
          ZPoly.congr_mul qFactor h 0 h m hqr.1 (ZPoly.congr_refl h m)
      exact ZPoly.congr_trans (mulModSquare qFactor h m) (qFactor * h) 0 m
        (congr_of_square_mod m (mulModSquare qFactor h m) (qFactor * h) hqhSq)
        hmulBase
    have hadd :
        ZPoly.congr
          (addModSquare (mulModSquare s e m) (mulModSquare qFactor h m) m)
          (mulModSquare s e m + mulModSquare qFactor h m)
          (m * m) :=
      addModSquare_congr m (mulModSquare s e m) (mulModSquare qFactor h m) hm0
    have hsum : ZPoly.congr (mulModSquare s e m + mulModSquare qFactor h m) 0 m := by
      simpa [DensePoly.zero_add] using
        ZPoly.congr_add (mulModSquare s e m) (mulModSquare qFactor h m) 0 0 m hse hqh
    exact ZPoly.congr_trans hCorrection
      (mulModSquare s e m + mulModSquare qFactor h m) 0 m
      (congr_of_square_mod m hCorrection
        (mulModSquare s e m + mulModSquare qFactor h m)
        (by simpa [hCorrection] using hadd))
      hsum
  have hh' : ZPoly.congr h' h m := by
    have hadd : ZPoly.congr (addModSquare h hCorrection m) (h + hCorrection) (m * m) :=
      addModSquare_congr m h hCorrection hm0
    have hbase : ZPoly.congr (h + hCorrection) (h + 0) m :=
      ZPoly.congr_add h hCorrection h 0 m (ZPoly.congr_refl h m) hCorrection_zero
    exact ZPoly.congr_trans h' (h + hCorrection) h m
      (congr_of_square_mod m h' (h + hCorrection) (by simpa [h'] using hadd))
      (by simpa [hzero_add] using hbase)
  exact ⟨hg', hh'⟩

end ZPoly
end Hex
