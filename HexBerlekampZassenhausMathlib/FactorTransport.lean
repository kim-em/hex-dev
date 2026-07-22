/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.FactorSoundness
public import HexBerlekampZassenhaus.IrreducibleDecide
public import HexBerlekampZassenhaus.Factored
public import HexBerlekampMathlib.FactorPoly

public section

/-!
Kernel-decidable assemblers for the `Polynomial ℤ` / strong `Hex.ZPoly`
provider of `factor_poly`/`irreducibility`.

Per-factor irreducibility is certified by one of two witness kinds: a
free-layer `Hex.ZPoly.IrredWitness` (prime constant / primitive linear /
single-prime modular certificate) or a multi-prime degree-obstruction
certificate `Hex.ZPolyIrreducibilityCertificate` for balanced factors with no
single-prime witness. `checkMultiPrimeCover` is the bulk Boolean check
covering a factor list by both kinds at once; `Hex.FactoredPoly.ofZ` and
`irreducible_ofZ` are the assemblers the provider emits, taking only Boolean
checks on reified literals (discharged by `Eq.refl true` in emitted terms)
plus one parser-built bridge equation `toPolynomial f = P`. The factorizer
and certificate generators never appear in emitted terms.
-/

namespace HexBerlekampZassenhausMathlib

/-- `toPolynomial` sends the executable `X` (the dense coefficient array
`#[0, 1]`) to Mathlib's `Polynomial.X`. -/
theorem toPolynomial_X :
    HexPolyZMathlib.toPolynomial (Hex.DensePoly.ofCoeffs #[0, 1]) = Polynomial.X := by
  ext n
  rw [HexPolyZMathlib.coeff_toPolynomial, Hex.DensePoly.coeff_ofCoeffs,
    Polynomial.coeff_X]
  match n with
  | 0 => simp
  | 1 => simp
  | n + 2 => rfl

/-- List products commute with the integer polynomial transport. -/
theorem toPolynomial_listProd (l : List Hex.ZPoly) :
    HexPolyZMathlib.toPolynomial l.prod =
      (l.map HexPolyZMathlib.toPolynomial).prod := by
  induction l with
  | nil => exact HexPolyZMathlib.toPolynomial_one
  | cons a t ih =>
      show HexPolyZMathlib.toPolynomial (a * t.prod) = _
      rw [HexPolyZMathlib.toPolynomial_mul, ih, List.map_cons, List.prod_cons]

/-- The decide-slot form of `checkIrreducibleCertLinear` soundness concluding
in the free layer: the same four Boolean hypotheses as
`irreducible_of_checkIrreducibleCertLinear`, with the Mathlib-free
`Hex.ZPoly.Irreducible` conclusion transported back through the
unconditional `Irreducible_iff_polynomialIrreducible`. -/
theorem zpolyIrreducible_of_checkIrreducibleCertLinear
    (f : Hex.ZPoly) (cert : Hex.ZPolyIrreducibilityCertificate)
    (hprime : cert.perPrime.all (fun primeData => decide (Nat.Prime primeData.p)) = true)
    (hcontent : decide (Hex.ZPoly.content f = 1) = true)
    (hpos : decide (0 < f.degree?.getD 0) = true)
    (hcert : Hex.checkIrreducibleCertLinear f cert = true) :
    Hex.ZPoly.Irreducible f :=
  (Hex.ZPoly.Irreducible_iff_polynomialIrreducible f).mpr
    (irreducible_of_checkIrreducibleCertLinear f cert hprime hcontent hpos hcert)

/-- Kernel-decidable check that a multi-prime certificate witnesses
irreducibility of `f`: primality of the recorded block primes, content one,
positive executable degree, and the incremental pow-chain replay
`checkIrreducibleCertLinear` — the four hypothesis slots of
`zpolyIrreducible_of_checkIrreducibleCertLinear` as one Boolean. -/
@[expose]
def checkMultiPrimeCert (f : Hex.ZPoly)
    (cert : Hex.ZPolyIrreducibilityCertificate) : Bool :=
  cert.perPrime.all (fun primeData => decide (Nat.Prime primeData.p)) &&
    decide (Hex.ZPoly.content f = 1) &&
    decide (0 < f.degree?.getD 0) &&
    Hex.checkIrreducibleCertLinear f cert

/-- A passing `checkMultiPrimeCert` forces free-layer irreducibility. -/
theorem zpolyIrreducible_of_checkMultiPrimeCert
    (f : Hex.ZPoly) (cert : Hex.ZPolyIrreducibilityCertificate)
    (hcheck : checkMultiPrimeCert f cert = true) :
    Hex.ZPoly.Irreducible f := by
  unfold checkMultiPrimeCert at hcheck
  simp only [Bool.and_eq_true] at hcheck
  obtain ⟨⟨⟨hprime, hcontent⟩, hpos⟩, hcert⟩ := hcheck
  exact zpolyIrreducible_of_checkIrreducibleCertLinear f cert hprime hcontent hpos hcert

/-- Bulk kernel-decidable irreducibility for a `ZPoly` factor list with
repetition, mixing witness kinds: `certified` carries free-layer
`IrredWitness` entries, `multiPrime` carries multi-prime degree-obstruction
certificates for balanced factors, and every factor must match one of the two
lists by `beqCoeffs`. -/
@[expose]
def checkMultiPrimeCover (factors : List Hex.ZPoly)
    (certified : List (Hex.ZPoly × Hex.ZPoly.IrredWitness))
    (multiPrime : List (Hex.ZPoly × Hex.ZPolyIrreducibilityCertificate)) : Bool :=
  (certified.all fun e => Hex.ZPoly.checkIrredWitness e.1 e.2) &&
    (multiPrime.all fun e => checkMultiPrimeCert e.1 e.2) &&
    (factors.all fun q =>
      (certified.any fun e => Hex.DensePoly.beqCoeffs e.1 q) ||
        (multiPrime.any fun e => Hex.DensePoly.beqCoeffs e.1 q))

/-- A passing `checkMultiPrimeCover` forces free-layer irreducibility of every
listed factor. -/
theorem irreducible_of_checkMultiPrimeCover
    (factors : List Hex.ZPoly)
    (certified : List (Hex.ZPoly × Hex.ZPoly.IrredWitness))
    (multiPrime : List (Hex.ZPoly × Hex.ZPolyIrreducibilityCertificate))
    (hcheck : checkMultiPrimeCover factors certified multiPrime = true) :
    ∀ q ∈ factors, Hex.ZPoly.Irreducible q := by
  unfold checkMultiPrimeCover at hcheck
  simp only [Bool.and_eq_true] at hcheck
  obtain ⟨⟨hcert, hmulti⟩, hcover⟩ := hcheck
  rw [List.all_eq_true] at hcert hmulti hcover
  intro q hq
  have hq' := hcover q hq
  rw [Bool.or_eq_true] at hq'
  rcases hq' with h | h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hbeq⟩ := h
    have hw := Hex.ZPoly.irreducible_of_checkIrredWitness e.1 e.2 (hcert e he)
    rwa [Hex.DensePoly.eq_of_beqCoeffs hbeq] at hw
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hbeq⟩ := h
    have hw := zpolyIrreducible_of_checkMultiPrimeCert e.1 e.2 (hmulti e he)
    rwa [Hex.DensePoly.eq_of_beqCoeffs hbeq] at hw

/-- Decide-slot endpoint for the `irreducibility!` kernel fallback on
`Hex.ZPoly`: the kernel replays the full factorizer through
`Hex.ZPoly.instDecidableIrreducible`. Emitted only by the bang forms; see
their docstrings for the cost and `import all` closure caveats. -/
theorem _root_.Hex.ZPoly.irreducible_of_decide (f : Hex.ZPoly)
    (h : decide (Hex.ZPoly.Irreducible f) = true) : Hex.ZPoly.Irreducible f :=
  of_decide_eq_true h

/-- Bulk decide-slot endpoint for the `factor_poly!` kernel fallback on
`Hex.ZPoly`: one kernel factorizer replay per listed factor. -/
theorem _root_.Hex.ZPoly.forall_irreducible_of_decide (l : List Hex.ZPoly)
    (h : decide (∀ q ∈ l, Hex.ZPoly.Irreducible q) = true) :
    ∀ q ∈ l, Hex.ZPoly.Irreducible q :=
  of_decide_eq_true h

/-- Decide-slot endpoint for the `irreducibility!` kernel fallback on
`Polynomial ℤ`: the free-layer kernel replay transported through the
unconditional iff and the parser-built bridge equation. -/
theorem irreducible_ofZ_decide (P : Polynomial ℤ) (f : Hex.ZPoly)
    (h : decide (Hex.ZPoly.Irreducible f) = true)
    (hP : HexPolyZMathlib.toPolynomial f = P) : Irreducible P := by
  rw [← hP]
  exact (Hex.ZPoly.Irreducible_iff_polynomialIrreducible f).mp (of_decide_eq_true h)

/-- Single-polynomial endpoint for the `irreducibility` provider on
`Polynomial ℤ`: the cover check on the singleton factor list accepts either
witness kind, and `hP` is the parser-built bridge equation. -/
theorem irreducible_ofZ (P : Polynomial ℤ) (f : Hex.ZPoly)
    (certified : List (Hex.ZPoly × Hex.ZPoly.IrredWitness))
    (multiPrime : List (Hex.ZPoly × Hex.ZPolyIrreducibilityCertificate))
    (hcover : checkMultiPrimeCover [f] certified multiPrime = true)
    (hP : HexPolyZMathlib.toPolynomial f = P) : Irreducible P := by
  have h := irreducible_of_checkMultiPrimeCover [f] certified multiPrime hcover f
    List.mem_cons_self
  rw [← hP]
  exact (Hex.ZPoly.Irreducible_iff_polynomialIrreducible f).mp h

end HexBerlekampZassenhausMathlib

namespace Hex

open HexBerlekampZassenhausMathlib

/-- One-shot assembler for the `factor_poly` provider on `Polynomial ℤ`:
every certification slot is a Boolean check on reified literal data (filled by
`Eq.refl true` in emitted terms), and `hP` is the parser-built bridge equation
tying the reified executable polynomial to the user's Mathlib polynomial. -/
@[expose]
noncomputable def FactoredPoly.ofZ (P : Polynomial ℤ) (f : Hex.ZPoly) (s : Int)
    (factors : List Hex.ZPoly)
    (certified : List (Hex.ZPoly × Hex.ZPoly.IrredWitness))
    (multiPrime : List (Hex.ZPoly × Hex.ZPolyIrreducibilityCertificate))
    (hmul : Hex.DensePoly.beqCoeffs (Hex.DensePoly.C s * factors.prod) f = true)
    (hcover : checkMultiPrimeCover factors certified multiPrime = true)
    (hP : HexPolyZMathlib.toPolynomial f = P) : Hex.FactoredPoly P where
  scalar := s
  factors := factors.map HexPolyZMathlib.toPolynomial
  factors_mul := by
    calc Polynomial.C s * (factors.map HexPolyZMathlib.toPolynomial).prod
        = HexPolyZMathlib.toPolynomial (Hex.DensePoly.C s) *
            HexPolyZMathlib.toPolynomial factors.prod := by
          rw [HexPolyZMathlib.toPolynomial_C, toPolynomial_listProd]
      _ = HexPolyZMathlib.toPolynomial (Hex.DensePoly.C s * factors.prod) :=
          (HexPolyZMathlib.toPolynomial_mul _ _).symm
      _ = HexPolyZMathlib.toPolynomial f := by rw [Hex.DensePoly.eq_of_beqCoeffs hmul]
      _ = P := hP
  factors_irred := by
    intro q hq
    rw [List.mem_map] at hq
    obtain ⟨g, hg, rfl⟩ := hq
    exact (Hex.ZPoly.Irreducible_iff_polynomialIrreducible g).mp
      (irreducible_of_checkMultiPrimeCover factors certified multiPrime hcover g hg)

/-- Decide-slot assembler for the `factor_poly!` kernel fallback on
`Polynomial ℤ`: the `factors_irred` slot replays the full factorizer in the
kernel once per factor. Emitted only by the bang forms. -/
@[expose]
noncomputable def FactoredPoly.ofZDecide (P : Polynomial ℤ) (f : Hex.ZPoly)
    (s : Int) (factors : List Hex.ZPoly)
    (hmul : Hex.DensePoly.beqCoeffs (Hex.DensePoly.C s * factors.prod) f = true)
    (hirr : decide (∀ q ∈ factors, Hex.ZPoly.Irreducible q) = true)
    (hP : HexPolyZMathlib.toPolynomial f = P) : Hex.FactoredPoly P where
  scalar := s
  factors := factors.map HexPolyZMathlib.toPolynomial
  factors_mul := by
    calc Polynomial.C s * (factors.map HexPolyZMathlib.toPolynomial).prod
        = HexPolyZMathlib.toPolynomial (Hex.DensePoly.C s) *
            HexPolyZMathlib.toPolynomial factors.prod := by
          rw [HexPolyZMathlib.toPolynomial_C, toPolynomial_listProd]
      _ = HexPolyZMathlib.toPolynomial (Hex.DensePoly.C s * factors.prod) :=
          (HexPolyZMathlib.toPolynomial_mul _ _).symm
      _ = HexPolyZMathlib.toPolynomial f := by rw [Hex.DensePoly.eq_of_beqCoeffs hmul]
      _ = P := hP
  factors_irred := by
    intro q hq
    rw [List.mem_map] at hq
    obtain ⟨g, hg, rfl⟩ := hq
    exact (Hex.ZPoly.Irreducible_iff_polynomialIrreducible g).mp
      (of_decide_eq_true hirr g hg)

end Hex
