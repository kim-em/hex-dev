/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyFp.Frobenius
import HexPolyFp.ModCompose
import HexPolyFp.NttMul
import HexPolyFp.PrimeField
import HexPolyFp.SquareFree
import HexPolyFast.HalfGcd
import LeanBench

/-!
Benchmark registrations for `hex-poly-fp`.

This Phase 4 slice measures the executable finite-field polynomial operations
over fixed word-prime fields: the quotient-ring benchmarks use `F_65537`, and
the square-free/product benchmarks use `F_5`. Input construction is hoisted into
`prep`; timed targets return compact checksums or decomposition summaries.

Scientific registrations:

* `runMulSchoolbookChecksum`, `runMulPackedChecksum`,
  `runMulKaratsubaChecksum`, `runMulDirectNttChecksum`,
  `runMulCrtNttChecksum`, and `runMulFastChecksum`: forced finite-field
  multiplication kernels and the public dispatcher on identical `F_65537`
  fixtures.  Direct NTT plan construction is hoisted into `prep`.
* `runMulDirectNttColdChecksum`: the same direct NTT path with checked plan
  construction included in the timed body.
* `runDivModFastChecksum` and `runGcdFastChecksum`: Newton division and
  half-gcd through `FpPoly.fastPlan`, paired with the retained field routines.
* `runFastPowChecksum`, `runFastFrobeniusChecksum`,
  `runFastFrobeniusPowChecksum`, and `runFastComposeChecksum`: end-to-end
  consumer candidates using `FpPoly.mulFast` with the retained monic
  reduction.

* `runPowModMonicChecksum`: quotient-ring square-and-multiply with a growing
  exponent, `O(n^2 log n)`.
* `runFrobeniusXModChecksum`: a batch of `n` calls to `X^p mod f` on degree
  `n` moduli, modeled by the 17 fixed-exponent squaring stages.
* `runFrobeniusXPowModChecksum`: `X^(p^n) mod f`, `O(n^3)` for growing modulus
  degree and Frobenius exponent height.
* `runComposeModMonicChecksum`: Horner modular composition, `O(n^3)`.
* `runWeightedProductChecksum`: product of `n` linear factors, `O(n^2)`.
* `runSquareFreeDecompositionSummary`: Yun-style square-free decomposition on
  deterministic product-shaped inputs, `O(n^2)`.
-/

namespace Hex
namespace FpPolyBench

open FpPoly

private instance benchBoundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩
private instance benchBoundsFermat : ZMod64.Bounds 257 := ⟨by decide, by decide⟩
private instance benchBoundsLarge : ZMod64.Bounds 65537 := ⟨by decide, by decide⟩

private theorem one_ne_zero_five : (1 : ZMod64 5) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 5) 1 0).mp h
  simp at hm

private theorem one_ne_zero_large : (1 : ZMod64 65537) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 65537) 1 0).mp h
  simp at hm

private theorem prime_five : Hex.Nat.Prime 5 := by
  constructor
  · decide
  · intro m hm
    have hmle : m ≤ 5 := Nat.le_of_dvd (by decide : 0 < 5) hm
    have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · simp at hm
    · exact Or.inl rfl
    · simp at hm
    · simp at hm
    · simp at hm
    · exact Or.inr rfl

private theorem prime_257 : Hex.Nat.Prime 257 :=
  Hex.Nat.prime_of_bounded 257 16 (by decide) (by decide) (by decide)

set_option maxRecDepth 8192 in
private theorem prime_65537 : Hex.Nat.Prime 65537 :=
  Hex.Nat.prime_of_bounded 65537 256 (by decide) (by decide) (by decide)

private instance benchPrimeLarge : ZMod64.PrimeModulus 65537 :=
  ZMod64.primeModulusOfPrime prime_65537

private instance benchPrimeFermat : ZMod64.PrimeModulus 257 :=
  ZMod64.primeModulusOfPrime prime_257

instance {p : Nat} [ZMod64.Bounds p] : Hashable (ZMod64 p) where
  hash a := hash a.toNat

instance {p : Nat} [ZMod64.Bounds p] : Hashable (FpPoly p) where
  hash f := hash f.toArray

instance : Hashable (SquareFreeFactor 5) where
  hash sf := mixHash (hash sf.factor) (hash sf.multiplicity)

/-- Prepared input for quotient-ring exponentiation and Frobenius operations. -/
structure ModInput where
  base : FpPoly 65537
  degree : Nat
  exponent : Nat
  deriving Hashable

/-- Prepared batched input for fixed-prime Frobenius. -/
structure FrobeniusBatchInput where
  count : Nat
  degree : Nat
  deriving Hashable

/-- Prepared input for modular composition. -/
structure ComposeInput where
  outer : FpPoly 65537
  inner : FpPoly 65537
  degree : Nat
  deriving Hashable

/-- Prepared input for weighted products. -/
structure WeightedInput where
  factors : List (SquareFreeFactor 5)
  deriving Hashable

/-- Prepared input for square-free decomposition. -/
structure SquareFreeInput where
  poly : FpPoly 5
  deriving Hashable

/-- Prepared input for field long division: a dividend and a lower-degree divisor. -/
structure DivModInput where
  num : FpPoly 65537
  den : FpPoly 65537
  deriving Hashable

/-- Prepared input for the Euclidean gcd remainder sequence over `F_p`. -/
structure GcdInput where
  f : FpPoly 65537
  g : FpPoly 65537
  deriving Hashable

/-- Prepared operands shared by finite-field multiplication kernels. -/
structure MulInput where
  left : FpPoly 65537
  right : FpPoly 65537
  deriving Hashable

/-- Prepared operands over the smaller Fermat prime in the modulus ladder. -/
structure MulInput257 where
  left : FpPoly 257
  right : FpPoly 257
  deriving Hashable

/-- Multiplication operands paired with a checked reusable target-modulus NTT
plan.  The plan length is retained as an index, so an ill-sized plan cannot be
passed to the direct kernel. -/
structure DirectMulInput where
  length : Nat
  plan : ZMod64.NttPlan 65537 length
  left : FpPoly 65537
  right : FpPoly 65537

instance : Hashable DirectMulInput where
  hash input := mixHash (hash input.left) (hash input.right)

/-- `F_257` operands paired with a checked reusable direct-NTT plan. -/
structure DirectMulInput257 where
  length : Nat
  plan : ZMod64.NttPlan 257 length
  left : FpPoly 257
  right : FpPoly 257

instance : Hashable DirectMulInput257 where
  hash input := mixHash (hash input.left) (hash input.right)

/-- Deterministic coefficient generator keyed by size, index, and salt. -/
def coeffValueFive (n i salt : Nat) : ZMod64 5 :=
  ZMod64.ofNat 5 <|
    ((i + 1) * (salt + 17) + (i + 3) * (i + 5) * 13 + n * 29) % 5

/-- Deterministic large-prime coefficient generator keyed by size, index, and salt. -/
def coeffValueLarge (n i salt : Nat) : ZMod64 65537 :=
  ZMod64.ofNat 65537 <|
    ((i + 1) * (salt + 17) + (i + 3) * (i + 5) * 13 + n * 29) % 65537

/-- Deterministic dense finite-field polynomial with `n` generated coefficients. -/
def densePolyFive (n salt : Nat) : FpPoly 5 :=
  ofCoeffs <| (Array.range n).map fun i => coeffValueFive n i salt

/-- Deterministic dense polynomial over the large benchmark prime field. -/
def densePolyLarge (n salt : Nat) : FpPoly 65537 :=
  ofCoeffs <| (Array.range n).map fun i => coeffValueLarge n i salt

/-- Deterministic dense polynomial over `F_257`. -/
def densePoly257 (n salt : Nat) : FpPoly 257 :=
  ofCoeffs <| (Array.range n).map fun i =>
    ZMod64.ofNat 257 <|
      ((i + 1) * (salt + 17) + (i + 3) * (i + 5) * 13 + n * 29) % 257

/-- Deterministic monic modulus of degree `degree` over `F_5`. -/
def monicModulusFive (degree : Nat) : FpPoly 5 :=
  DensePoly.monomial degree (1 : ZMod64 5)

/-- Generated monomial moduli over `F_5` are monic. -/
theorem monicModulusFive_monic (degree : Nat) : DensePoly.Monic (monicModulusFive degree) := by
  unfold monicModulusFive DensePoly.Monic DensePoly.leadingCoeff DensePoly.monomial
  by_cases h : (1 : ZMod64 5) = 0
  · exact False.elim (one_ne_zero_five h)
  · have h' : ¬ ((1 : ZMod64 5) = Zero.zero) := h
    simp only [dif_neg h']
    simp [Array.getElem_push] <;> rfl

/-- Deterministic monic modulus of degree `degree` over the large benchmark prime. -/
def monicModulusLarge (degree : Nat) : FpPoly 65537 :=
  { coeffs := ((Array.range degree).map fun i => coeffValueLarge degree i 503).push 1
    normalized := by
      right
      intro hback
      have hlast :
          (((Array.range degree).map fun i => coeffValueLarge degree i 503).push
              (1 : ZMod64 65537)).back? = some 1 := by
        simp
      rw [hlast] at hback
      exact one_ne_zero_large (Option.some.inj hback) }

/-- Generated monomial moduli over the large benchmark prime are monic. -/
theorem monicModulusLarge_monic (degree : Nat) :
    DensePoly.Monic (monicModulusLarge degree) := by
  unfold monicModulusLarge DensePoly.Monic DensePoly.leadingCoeff
  simp [Array.getElem_push] <;> rfl

/-- Deterministic linear square-free factor. -/
def linearFactor (i : Nat) : FpPoly 5 :=
  ofCoeffs #[coeffValueFive i 0 211, 1]

/-- Deterministic factor record used by weighted-product benchmarks. -/
def weightedFactor (i : Nat) : SquareFreeFactor 5 :=
  { factor := linearFactor i, multiplicity := 1 }

/--
Balanced multiplicity distribution for the square-free decomposition fixture.

The five distinct monic linear factors `(x - 0), (x - 1), …, (x - 4)` over
`F_5` are assigned multiplicities `⌊n / 5⌋` each, with the first `n mod 5`
factors taking an extra `+1`. The resulting product has total degree exactly
`n`, exactly five distinct linear factors, and max multiplicity `⌈n / 5⌉`,
giving a Yun ladder whose iteration count grows linearly with `n` and whose
per-iteration `gcd(c, w)` and `w / y` calls each scale linearly with the
shrinking remnant degree.

The fixture cannot avoid the formal-`p`-th-root branch entirely: when at
least one multiplicity divides `p = 5`, the contribution of that factor to
`f'` vanishes and the squarefree part `c_0` collapses to fewer distinct
factors than the polynomial actually contains. The constant in front of
`n^2` then increases (the Yun ladder takes more shrink steps before
exhausting `c_0`), but the asymptote stays `O(n^2)`. The scientific
schedule avoids the worst-case rung where four out of five multiplicities
divide `5` simultaneously.
-/
def balancedSquareFreeFactors (n : Nat) : List (SquareFreeFactor 5) :=
  let base := n / 5
  let rem := n % 5
  (List.range 5).map fun i =>
    { factor := ofCoeffs #[ZMod64.ofNat 5 i, 1]
      multiplicity := if i < rem then base + 1 else base }

/-- Stable checksum for polynomial-valued benchmark results. -/
def checksumPoly {p : Nat} [ZMod64.Bounds p] (f : FpPoly p) : UInt64 :=
  f.toArray.foldl (fun acc coeff => mixHash acc (hash coeff)) 0

/-- Stable bounded summary for square-free decompositions. -/
def checksumSquareFree (d : SquareFreeDecomposition 5) : UInt64 :=
  d.factors.foldl
    (fun acc sf => mixHash (mixHash acc (checksumPoly sf.factor)) (hash sf.multiplicity))
    (hash d.unit)

/-- Per-parameter fixture for quotient-ring exponentiation. -/
def prepPowModInput (n : Nat) : ModInput :=
  { base := densePolyLarge (n + 1) 11
    degree := n + 1
    exponent := n + 1 }

/-- Per-parameter fixture for fixed-prime Frobenius batches. -/
def prepFrobeniusInput (n : Nat) : FrobeniusBatchInput :=
  { count := n
    degree := n + 1 }

/-- Per-parameter fixture for Frobenius powers. -/
def prepFrobeniusPowInput (n : Nat) : ModInput :=
  { base := X
    degree := n + 1
    exponent := n + 1 }

/-- Per-parameter fixture for same-size modular composition. -/
def prepComposeInput (n : Nat) : ComposeInput :=
  { outer := densePolyLarge (n + 1) 37
    inner := densePolyLarge (n + 1) 71
    degree := n + 1 }

/-- Per-parameter fixture for weighted products of linear factors. -/
def prepWeightedInput (n : Nat) : WeightedInput :=
  { factors := (List.range n).map weightedFactor }

/-- Per-parameter fixture for square-free decomposition. -/
def prepSquareFreeInput (n : Nat) : SquareFreeInput :=
  { poly := weightedProduct (balancedSquareFreeFactors n) }

/-- Per-parameter fixture for field long division: a degree-`2n` dividend over a
degree-`n` divisor, so the division loop runs `Θ(n)` elimination steps. -/
def prepDivModInput (n : Nat) : DivModInput :=
  { num := densePolyLarge (2 * n + 1) 17
    den := densePolyLarge (n + 1) 23 }

/-- Per-parameter fixture for the Euclidean gcd remainder sequence.

Starting from `(F₀, F₁) = (0, 1)`, the recurrence
`Fₖ₊₂ = X * Fₖ₊₁ + Fₖ` makes `(Fₙ₊₁, Fₙ)` a coprime consecutive pair whose
Euclidean remainder sequence has exactly `n` degree-one quotient steps. -/
def prepGcdInput (n : Nat) : GcdInput :=
  let pair := (List.range n).foldl
    (fun state _ => (state.2, X * state.2 + state.1))
    ((0 : FpPoly 65537), (1 : FpPoly 65537))
  { f := pair.2
    g := pair.1 }

/-- Family-specific work model for a batch of fixed-prime Frobenius calls.

The exponent `65537 = 2^16 + 1` gives 17 squaring stages.  Before reduction
saturates at modulus degree `n`, stage `k` squares a polynomial of degree
`min n (2^k)`; afterward every stage remains at degree `n`.  Schoolbook
multiplication and monic reduction therefore have the same order as the sum
of these squared active degrees, repeated for all `n` calls in the batch. -/
def frobeniusWork (n : Nat) : Nat :=
  (List.range 17).foldl (fun total k =>
    let degree := min n (2 ^ k)
    total + n * degree * degree) 0

/-- Balanced dense multiplication fixture over the large benchmark prime. -/
def prepMulInput (n : Nat) : MulInput :=
  { left := densePolyLarge n 101
    right := densePolyLarge n 211 }

/-- Balanced dense multiplication fixture over `F_257`. -/
def prepMulInput257 (n : Nat) : MulInput257 :=
  { left := densePoly257 n 101
    right := densePoly257 n 211 }

/-- Build the checked target-modulus plan for a prepared product.  The residue
`3` has order `65536` modulo `65537`; exponentiating it by the transform stride
derives the exact-order root checked by `NttPlan.build?`. -/
def directMulInput? (input : MulInput) : Option DirectMulInput := do
  let length := (input.left.size + input.right.size - 1).nextPowerOfTwo
  let root : ZMod64 65537 :=
    (ZMod64.ofNat 65537 3) ^ (65536 / length)
  let plan ← ZMod64.NttPlan.build? (n := length) root
  pure { length, plan, left := input.left, right := input.right }

/-- Prepared reusable-plan direct NTT input. -/
def prepDirectMulInput (n : Nat) : Option DirectMulInput :=
  directMulInput? (prepMulInput n)

/-- Build a reusable direct plan over `F_257`, whose element `3` has order
`256`.  The largest registered operand size `128` therefore uses transform
length `256`, exactly at this modulus's radix-two limit. -/
def directMulInput257? (input : MulInput257) : Option DirectMulInput257 := do
  let length := (input.left.size + input.right.size - 1).nextPowerOfTwo
  let root : ZMod64 257 :=
    (ZMod64.ofNat 257 3) ^ (256 / length)
  let plan ← ZMod64.NttPlan.build? (n := length) root
  pure { length, plan, left := input.left, right := input.right }

def prepDirectMulInput257 (n : Nat) : Option DirectMulInput257 :=
  directMulInput257? (prepMulInput257 n)

/-- Reduce one fast-dispatch product with the retained monic long division. -/
def mulModFast (left right modulus : FpPoly 65537)
    (hmonic : DensePoly.Monic modulus) : FpPoly 65537 :=
  modByMonic modulus (mulFast left right) hmonic

/-- Reduce one schoolbook product with the retained monic long division. -/
def mulModSchoolbook (left right modulus : FpPoly 65537)
    (hmonic : DensePoly.Monic modulus) : FpPoly 65537 :=
  modByMonic modulus (left * right) hmonic

/-- One-shot schoolbook modular power reference. -/
def powModSchoolbook (base modulus : FpPoly 65537)
    (hmonic : DensePoly.Monic modulus) (exponent : Nat) : FpPoly 65537 :=
  FpPoly.powModMonicAux modulus hmonic exponent
    (modByMonic modulus base hmonic) 1

/-- Square-and-multiply candidate using fast coefficient multiplication but
the retained monic reduction. -/
def powModFastAux (modulus : FpPoly 65537) (hmonic : DensePoly.Monic modulus) :
    Nat → FpPoly 65537 → FpPoly 65537 → FpPoly 65537
  | 0, _, acc => acc
  | n + 1, base, acc =>
      let acc' :=
        if (n + 1) % 2 = 0 then acc else mulModFast acc base modulus hmonic
      let base' := mulModFast base base modulus hmonic
      powModFastAux modulus hmonic ((n + 1) / 2) base' acc'
termination_by n => n
decreasing_by
  simpa using Nat.div_lt_self (Nat.succ_pos n) (by decide : 1 < 2)

/-- One-shot fast-multiply modular power candidate. -/
def powModFast (base modulus : FpPoly 65537) (hmonic : DensePoly.Monic modulus)
    (exponent : Nat) : FpPoly 65537 :=
  powModFastAux modulus hmonic exponent (modByMonic modulus base hmonic) 1

/-- Benchmark target: compute `base^exponent mod modulus`. -/
def runPowModMonicChecksum (input : ModInput) : UInt64 :=
  checksumPoly <|
    powModSchoolbook input.base (monicModulusLarge input.degree)
      (monicModulusLarge_monic input.degree)
      input.exponent

/-- Benchmark candidate: modular power with fast multiplication. -/
def runFastPowChecksum (input : ModInput) : UInt64 :=
  checksumPoly <|
    powModFast input.base (monicModulusLarge input.degree)
      (monicModulusLarge_monic input.degree) input.exponent

/-- Benchmark target: compute a batch of `X^p mod modulus` calls. -/
def runFrobeniusXModChecksum (input : FrobeniusBatchInput) : UInt64 :=
  (Array.range input.count).foldl
    (fun acc _ =>
      mixHash acc <| checksumPoly <|
        powModSchoolbook X (monicModulusLarge input.degree)
          (monicModulusLarge_monic input.degree) 65537)
    0

/-- Benchmark candidate: batched Frobenius with fast multiplication. -/
def runFastFrobeniusChecksum (input : FrobeniusBatchInput) : UInt64 :=
  (Array.range input.count).foldl
    (fun acc _ =>
      mixHash acc <| checksumPoly <|
        powModFast X (monicModulusLarge input.degree)
          (monicModulusLarge_monic input.degree) 65537)
    0

/-- Benchmark target: compute `X^(p^k) mod modulus`. -/
def runFrobeniusXPowModChecksum (input : ModInput) : UInt64 :=
  checksumPoly <|
    powModSchoolbook X (monicModulusLarge input.degree)
      (monicModulusLarge_monic input.degree) (65537 ^ input.exponent)

/-- Benchmark candidate: high Frobenius power with fast multiplication. -/
def runFastFrobeniusPowChecksum (input : ModInput) : UInt64 :=
  checksumPoly <|
    powModFast X (monicModulusLarge input.degree)
      (monicModulusLarge_monic input.degree) (65537 ^ input.exponent)

/-- Benchmark target: compute modular composition and checksum the result. -/
def runComposeModMonicChecksum (input : ComposeInput) : UInt64 :=
  let modulus := monicModulusLarge input.degree
  let hmonic := monicModulusLarge_monic input.degree
  checksumPoly <| input.outer.toArray.foldr
    (fun coeff acc => modByMonic modulus (acc * input.inner + C coeff) hmonic)
    0

/-- Benchmark candidate: modular Horner composition with fast multiplication. -/
def runFastComposeChecksum (input : ComposeInput) : UInt64 :=
  let modulus := monicModulusLarge input.degree
  let hmonic := monicModulusLarge_monic input.degree
  checksumPoly <| input.outer.toArray.foldr
    (fun coeff acc => modByMonic modulus (mulFast acc input.inner + C coeff) hmonic)
    0

/-- Benchmark target: multiply weighted square-free factors. -/
def runWeightedProductChecksum (input : WeightedInput) : UInt64 :=
  checksumPoly <| weightedProduct input.factors

/-- Benchmark target: compute a square-free decomposition summary. -/
def runSquareFreeDecompositionSummary (input : SquareFreeInput) : UInt64 :=
  checksumSquareFree <| squareFreeDecomposition prime_five input.poly

/-- Benchmark target: field long division, checksumming quotient and remainder. -/
def runDivModChecksum (input : DivModInput) : UInt64 :=
  let qr := DensePoly.divMod input.num input.den
  mixHash (checksumPoly qr.1) (checksumPoly qr.2)

/-- Benchmark candidate: Newton division through the finite-field fast plan. -/
def runDivModFastChecksum (input : DivModInput) : UInt64 :=
  let qr : FpPoly 65537 × FpPoly 65537 :=
    @DensePoly.divModWith (ZMod64 65537) inferInstance inferInstance
      (FpPoly.fastPlan (p := 65537)) input.num input.den
  mixHash (checksumPoly qr.1) (checksumPoly qr.2)

/-- Benchmark target: Euclidean gcd over `F_p`, checksumming the result. -/
def runGcdChecksum (input : GcdInput) : UInt64 :=
  checksumPoly <| DensePoly.gcd input.f input.g

/-- Benchmark candidate: half-gcd through the finite-field fast plan. -/
def runGcdFastChecksum (input : GcdInput) : UInt64 :=
  let result : FpPoly 65537 :=
    @DensePoly.gcdWith (ZMod64 65537) inferInstance inferInstance
      (FpPoly.fastPlan (p := 65537)) input.f input.g
  checksumPoly result

/-- Benchmark target: forced generic schoolbook multiplication. -/
def runMulSchoolbookChecksum (input : MulInput) : UInt64 :=
  checksumPoly (DensePoly.mulImpl input.left input.right)

/-- Benchmark target: forced packed lazy-reduction multiplication. -/
def runMulPackedChecksum (input : MulInput) : UInt64 :=
  checksumPoly (mulPacked input.left input.right)

/-- Benchmark target: forced generic Karatsuba multiplication. -/
def runMulKaratsubaChecksum (input : MulInput) : UInt64 :=
  checksumPoly (DensePoly.mulKaratsuba FpPoly.karatsubaCutoff input.left input.right)

/-- Benchmark target: direct target-modulus NTT with a plan reused from
fixture preparation. -/
def runMulDirectNttChecksum (input : Option DirectMulInput) : UInt64 :=
  match input with
  | none => 0
  | some input =>
      match mulNtt? input.plan input.left input.right with
      | some result => checksumPoly result
      | none => 0

/-- Benchmark target: direct target-modulus NTT including checked plan
construction in the timed body. -/
def runMulDirectNttColdChecksum (input : MulInput) : UInt64 :=
  runMulDirectNttChecksum (directMulInput? input)

/-- Benchmark target: forced auxiliary-prime CRT-NTT multiplication. -/
def runMulCrtNttChecksum (input : MulInput) : UInt64 :=
  match mulNttCrt? input.left input.right with
  | some result => checksumPoly result
  | none => 0

/-- Benchmark target: public finite-field multiplication dispatcher. -/
def runMulFastChecksum (input : MulInput) : UInt64 :=
  checksumPoly (mulFast input.left input.right)

/-- Forced generic schoolbook multiplication over `F_257`. -/
def runMulSchoolbook257Checksum (input : MulInput257) : UInt64 :=
  checksumPoly (DensePoly.mulImpl input.left input.right)

/-- Forced packed lazy-reduction multiplication over `F_257`. -/
def runMulPacked257Checksum (input : MulInput257) : UInt64 :=
  checksumPoly (mulPacked input.left input.right)

/-- Forced generic Karatsuba multiplication over `F_257`. -/
def runMulKaratsuba257Checksum (input : MulInput257) : UInt64 :=
  checksumPoly (DensePoly.mulKaratsuba FpPoly.karatsubaCutoff input.left input.right)

/-- Reusable-plan direct target-modulus NTT over `F_257`. -/
def runMulDirectNtt257Checksum (input : Option DirectMulInput257) : UInt64 :=
  match input with
  | none => 0
  | some input =>
      match mulNtt? input.plan input.left input.right with
      | some result => checksumPoly result
      | none => 0

/-- Forced auxiliary-prime CRT-NTT multiplication over `F_257`. -/
def runMulCrtNtt257Checksum (input : MulInput257) : UInt64 :=
  match mulNttCrt? input.left input.right with
  | some result => checksumPoly result
  | none => 0

/-- Public finite-field multiplication dispatcher over `F_257`. -/
def runMulFast257Checksum (input : MulInput257) : UInt64 :=
  checksumPoly (mulFast input.left input.right)

/-
The `F_257` registrations form the small-modulus half of the target-modulus
ladder.  All forced kernels share operands and rungs; the direct path reaches
transform length `256` at `n = 128`, exactly the two-adic capacity of `257 - 1`.
-/
/- Cost model: schoolbook convolution forms a quadratic number of coefficient
products in the balanced operand length. -/
setup_benchmark runMulSchoolbook257Checksum n => (n * n)
  with prep := prepMulInput257
  where {
    paramFloor := 4
    paramCeiling := 128
    paramSchedule := .custom #[4, 7, 8, 9, 16, 31, 32, 33, 64, 127, 128]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "forced", "balanced", "fp257"]
  }

/- Cost model: packed multiplication is bounded conservatively by the
quadratic schoolbook fallback on this finite ladder. -/
setup_benchmark runMulPacked257Checksum n => (n * n)
  with prep := prepMulInput257
  where {
    paramFloor := 4
    paramCeiling := 128
    paramSchedule := .custom #[4, 7, 8, 9, 16, 31, 32, 33, 64, 127, 128]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "forced", "balanced", "fp257"]
  }

/- Cost model: the three-subproblem Karatsuba recurrence is represented by
the integer-valued `n * sqrt n` surrogate. -/
setup_benchmark runMulKaratsuba257Checksum n => (n * Nat.sqrt n)
  with prep := prepMulInput257
  where {
    paramFloor := 4
    paramCeiling := 128
    paramSchedule := .custom #[4, 7, 8, 9, 16, 31, 32, 33, 64, 127, 128]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "forced", "balanced", "fp257"]
  }

/- Cost model: radix-two NTT has logarithmically many linear butterfly stages,
giving `O(n log n)` work with the plan prepared outside the timed body. -/
setup_benchmark runMulDirectNtt257Checksum n => (n * Nat.log2 (n + 1))
  with prep := prepDirectMulInput257
  where {
    paramFloor := 4
    paramCeiling := 128
    paramSchedule := .custom #[4, 7, 8, 9, 16, 31, 32, 33, 64, 127, 128]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "forced", "balanced", "fp257", "warm-plan"]
  }

/- Cost model: the fixed auxiliary-prime ladder performs a constant number of
radix-two transforms, preserving the `O(n log n)` bound. -/
setup_benchmark runMulCrtNtt257Checksum n => (n * Nat.log2 (n + 1))
  with prep := prepMulInput257
  where {
    paramFloor := 4
    paramCeiling := 128
    paramSchedule := .custom #[4, 7, 8, 9, 16, 31, 32, 33, 64, 127, 128]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "forced", "balanced", "fp257"]
  }

/- Cost model: the dispatcher is bounded conservatively by its retained
quadratic schoolbook kernel across this crossover ladder. -/
setup_benchmark runMulFast257Checksum n => (n * n)
  with prep := prepMulInput257
  where {
    paramFloor := 4
    paramCeiling := 128
    paramSchedule := .custom #[4, 7, 8, 9, 16, 31, 32, 33, 64, 127, 128]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "dispatch", "balanced", "fp257"]
  }

/-
Every warm registration uses the same deterministic operands and crossover
rungs.  The direct target-modulus entry alone uses the dependently typed plan
prepared outside the timed body; its cold companion exposes construction cost.
-/
/- Cost model: schoolbook convolution forms a quadratic number of coefficient
products in the balanced operand length. -/
setup_benchmark runMulSchoolbookChecksum n => (n * n)
  with prep := prepMulInput
  where {
    paramFloor := 16
    paramCeiling := 512
    paramSchedule := .custom #[16, 31, 32, 33, 64, 127, 128, 129, 256, 512]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "forced", "balanced", "fp65537"]
  }

/- Cost model: packed multiplication is bounded conservatively by the
quadratic schoolbook fallback while the measured rungs expose GMP regimes. -/
setup_benchmark runMulPackedChecksum n => (n * n)
  with prep := prepMulInput
  where {
    paramFloor := 16
    paramCeiling := 16384
    paramSchedule := .custom #[16, 31, 32, 33, 64, 127, 128, 129, 256, 512,
      1024, 2048, 4095, 4096, 4097, 8191, 8192, 8193, 16384]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "forced", "balanced", "fp65537"]
  }

/- Cost model: `n * sqrt n` is the nearest integer-valued built-in model to
`n^(log_2 3)`; crossover comparison, rather than the slope verdict, is the
purpose of this forced registration. -/
setup_benchmark runMulKaratsubaChecksum n => (n * Nat.sqrt n)
  with prep := prepMulInput
  where {
    paramFloor := 16
    paramCeiling := 16384
    paramSchedule := .custom #[16, 31, 32, 33, 64, 127, 128, 129, 256, 512,
      1024, 2048, 4095, 4096, 4097, 8191, 8192, 8193, 16384]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "forced", "balanced", "fp65537"]
  }

/- Cost model: radix-two NTT has logarithmically many linear butterfly stages,
giving `O(n log n)` work with a reusable plan. -/
setup_benchmark runMulDirectNttChecksum n => (n * Nat.log2 (n + 1))
  with prep := prepDirectMulInput
  where {
    paramFloor := 16
    paramCeiling := 16384
    paramSchedule := .custom #[16, 31, 32, 33, 64, 127, 128, 129, 256, 512,
      1024, 2048, 4095, 4096, 4097, 8191, 8192, 8193, 16384]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "forced", "balanced", "fp65537", "warm-plan"]
  }

/- Cost model: cold plan construction and the transform each use linear work
per logarithmic level, preserving the `O(n log n)` bound. -/
setup_benchmark runMulDirectNttColdChecksum n => (n * Nat.log2 (n + 1))
  with prep := prepMulInput
  where {
    paramFloor := 16
    paramCeiling := 16384
    paramSchedule := .custom #[16, 31, 32, 33, 64, 127, 128, 129, 256, 512,
      1024, 2048, 4095, 4096, 4097, 8191, 8192, 8193, 16384]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "forced", "balanced", "fp65537", "cold-plan"]
  }

/- Cost model: the fixed auxiliary-prime ladder performs a constant number of
radix-two transforms, preserving the `O(n log n)` bound. -/
setup_benchmark runMulCrtNttChecksum n => (n * Nat.log2 (n + 1))
  with prep := prepMulInput
  where {
    paramFloor := 16
    paramCeiling := 16384
    paramSchedule := .custom #[16, 31, 32, 33, 64, 127, 128, 129, 256, 512,
      1024, 2048, 4095, 4096, 4097, 8191, 8192, 8193, 16384]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "forced", "balanced", "fp65537"]
  }

/- Cost model: the dispatcher is bounded conservatively by its retained
quadratic schoolbook kernel across the full crossover ladder. -/
setup_benchmark runMulFastChecksum n => (n * n)
  with prep := prepMulInput
  where {
    paramFloor := 16
    paramCeiling := 16384
    paramSchedule := .custom #[16, 31, 32, 33, 64, 127, 128, 129, 256, 512,
      1024, 2048, 4095, 4096, 4097, 8191, 8192, 8193, 16384]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["multiplication", "dispatch", "balanced", "fp65537"]
  }

/-
The modulus degree, reduced base degree, and exponent all scale with `n`.
Square-and-multiply performs Theta(log n) quotient-ring multiplications, and
each reduced dense multiplication/reduction is quadratic in the modulus degree.
-/
setup_benchmark runPowModMonicChecksum n => n * n * Nat.log2 (n + 1)
  with prep := prepPowModInput
  where {
    paramFloor := 64
    paramCeiling := 512
    paramSchedule := .custom #[64, 96, 128, 192, 256, 384, 512]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Cost model: the fast path performs logarithmically many reduced products,
each conservatively quadratic in the modulus degree. -/
setup_benchmark runFastPowChecksum n => (n * n * Nat.log2 (n + 1))
  with prep := prepPowModInput
  where {
    paramFloor := 64
    paramCeiling := 512
    paramSchedule := .custom #[64, 96, 128, 192, 256, 384, 512]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["adoption", "power", "fast-multiply", "fp65537"]
  }

/-
Cost model: this batches `n` fixed-prime calls with reduced-base degree at most `n`
modulo dense degree-`n + 1` monic moduli. The model sums squared active degree over
the 17 squaring stages of `65537 = 2^16 + 1`: early stages grow as `2^k`, and
the remaining stages stay at modulus degree `n`.  Multiplying that sum by the
batch size accounts for the timed work without treating the decreasing number
of saturated stages as a constant.  The schedule starts at `n = 16`, above the
small-kernel startup regime, and ends at `n = 80`, well below the four-second
per-call cap on the reference host.
-/
setup_benchmark runFrobeniusXModChecksum n => frobeniusWork n
  with prep := prepFrobeniusInput
  where {
    paramFloor := 16
    paramCeiling := 80
    paramSchedule := .custom #[16, 24, 32, 48, 64, 80]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.20
  }

/- Cost model: the fast candidate traverses the same 17-stage active-degree schedule;
`frobeniusWork` is conservative and its ordered Phase-4 mode remains unresolved. -/
setup_benchmark runFastFrobeniusChecksum n => frobeniusWork n
  with prep := prepFrobeniusInput
  where {
    paramFloor := 16
    paramCeiling := 80
    paramSchedule := .custom #[16, 24, 32, 48, 64, 80]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.20
    tags := #["adoption", "frobenius", "fast-multiply", "fp65537"]
  }

/-
Here both the modulus degree and Frobenius height scale with `n`. The exponent
`65537^n` has Theta(n) bits, so the quotient-ring square-and-multiply loop performs
Theta(n) quadratic reduced multiplications. The schedule stops at `n = 64`
because at `n = 96` the per-call wall time crosses the four-second cap on the
reference host; trimming the truncating rung keeps every scheduled rung inside
the cap.
-/
setup_benchmark runFrobeniusXPowModChecksum n => n * n * n
  with prep := prepFrobeniusPowInput
  where {
    paramFloor := 16
    paramCeiling := 64
    paramSchedule := .custom #[16, 24, 32, 48, 64]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Cost model: the exponent has linearly many bits and each reduced product is
quadratic, giving a cubic conservative bound. -/
setup_benchmark runFastFrobeniusPowChecksum n => (n * n * n)
  with prep := prepFrobeniusPowInput
  where {
    paramFloor := 16
    paramCeiling := 64
    paramSchedule := .custom #[16, 24, 32, 48, 64]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["adoption", "frobenius-power", "fast-multiply", "fp65537"]
  }

/-
Horner modular composition does one reduced multiplication per coefficient of
the outer polynomial. With all reduced polynomials bounded by degree `n`, each
step is quadratic, for Theta(n^3) total work. The schedule stops at `n = 192`
because at `n = 256` the per-call wall time crosses the four-second cap on
the reference host; trimming the truncating rung keeps every scheduled rung
inside the cap.
-/
setup_benchmark runComposeModMonicChecksum n => n * n * n
  with prep := prepComposeInput
  where {
    paramFloor := 32
    paramCeiling := 192
    paramSchedule := .custom #[32, 48, 64, 96, 128, 192]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Cost model: Horner composition performs linearly many conservatively
quadratic reduced products, giving cubic work. -/
setup_benchmark runFastComposeChecksum n => (n * n * n)
  with prep := prepComposeInput
  where {
    paramFloor := 32
    paramCeiling := 192
    paramSchedule := .custom #[32, 48, 64, 96, 128, 192]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["adoption", "composition", "fast-multiply", "fp65537"]
  }

/-
The prepared family multiplies `n` linear factors, all with multiplicity one.
The accumulator degree grows linearly, so the schoolbook multiplications by a
linear polynomial sum to Theta(n^2).
-/
setup_benchmark runWeightedProductChecksum n => n * n
  with prep := prepWeightedInput
  where {
    paramFloor := 256
    paramCeiling := 4096
    paramSchedule := .custom #[256, 384, 512, 768, 1024, 1536, 2048, 3072, 4096]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
This prepared family is the balanced product `∏_{i=0..4} (x - i)^{m_i}` over
`F_5`, with multiplicities `m_i ∈ {⌊n/5⌋, ⌈n/5⌉}` summing to `n`. Yun's
algorithm runs an initial dense `gcd(f, f')` followed by `⌈n / 5⌉` ladder
iterations whose `gcd(c, w)` and `w / y` calls each scale linearly with the
shrinking remnant degree; total cost is `O(n^2)` for every rung, with a
constant that varies modestly depending on whether any of the five
multiplicities at that `n` divides `p = 5` (in which case the squarefree
part `c_0` collapses to fewer distinct factors and the Yun ladder takes
more shrink steps). The schedule stops at `n = 768` because at `n = 1024`
the rung `(205, 205, 205, 205, 204)` has four multiplicities divisible by
`5` simultaneously, collapsing `c_0` to a single linear factor and
amplifying that constant by an order of magnitude; the verdict is fit over
the remaining rungs where the constant is bounded. The widened slope
tolerance acknowledges the residual `n`-to-`n` constant variance that this
input family carries.
-/
setup_benchmark runSquareFreeDecompositionSummary n => n * n
  with prep := prepSquareFreeInput
  where {
    paramFloor := 64
    paramCeiling := 768
    paramSchedule := .custom #[64, 96, 128, 192, 256, 384, 512, 768]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.30
  }

/-
Field long division of a degree-`2n` dividend by a degree-`n` divisor runs
`Theta(n)` elimination steps, each subtracting a shifted scalar multiple of the
divisor across `Theta(n)` coefficients, so the work is quadratic, `O(n^2)`
total. The schedule covers the BHKS-relevant low degrees `8/16/32/64` plus
higher rungs so the quadratic slope is visible above the per-call constant.
-/
setup_benchmark runDivModChecksum n => n * n
  with prep := prepDivModInput
  where {
    paramFloor := 8
    paramCeiling := 2048
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Newton division has `O(M(n))` algebraic work.  With the currently selected
packed Fp kernel below the NTT crossover, the conservative registered model is
quadratic; the shared rungs and result hash gate any consumer adoption. -/
setup_benchmark runDivModFastChecksum n => (n * n)
  with prep := prepDivModInput
  where {
    paramFloor := 8
    paramCeiling := 2048
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["division", "newton", "candidate", "fp65537"]
  }

/-
The prepared inputs are consecutive polynomial Fibonacci values.  They force
exactly `n` Euclidean remainder steps with quotient `X`; each remainder-only
division is linear in the current degree, so the decreasing-degree costs sum
to `Theta(n^2)`.  This fixture isolates worst-case Euclidean step scaling; its
unit leading coefficients and monomial quotients do not assert the same
constant factor as a generic separability input `gcd(f, f')`.  The schedule
matches the divMod rungs.
-/
setup_benchmark runGcdChecksum n => n * n
  with prep := prepGcdInput
  where {
    paramFloor := 8
    paramCeiling := 2048
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Half-gcd performs `O(M(n) log n)` algebraic work.  The quadratic model is a
conservative fit while `FpPoly.fastPlan` retains packed multiplication on this
ladder; direct comparison with Euclid, not a slope claim, gates consumers. -/
setup_benchmark runGcdFastChecksum n => (n * n)
  with prep := prepGcdInput
  where {
    paramFloor := 8
    paramCeiling := 2048
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256, 512, 1024, 2048]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["gcd", "half-gcd", "candidate", "fp65537"]
  }

end FpPolyBench
end Hex

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
