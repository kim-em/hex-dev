/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexArith.Nat.Prime
public meta import HexBerlekamp.Factor
public meta import HexBerlekamp.Irreducibility
public meta import HexHensel.ModularPolynomial
public meta import HexHensel.Multifactor
public meta import HexHensel.QuadraticMultifactor
public meta import HexMatrix.Basic
public meta import HexPolyZ.Mignotte
public meta import HexLLL
public import HexArith.Nat.Prime
public import HexBerlekamp.Factor
public import HexBerlekamp.Irreducibility
public import HexHensel.Multifactor
public import HexHensel.QuadraticMultifactor
public import HexLLL
-- Kernel-reducible `Array`/`Vector` equality; see `HexBasic.ArrayDecEq`.
-- Drop once leanprover/lean4#14270 lands and the toolchain is bumped past it.
public import HexBasic.ArrayDecEq

public import HexBerlekampZassenhaus.PrimeSelection
public import HexBerlekampZassenhaus.SquareFreeModularCert
public meta import HexBerlekampZassenhaus.PrimeSelection
import all HexBerlekampZassenhaus.PrimeSelection

open scoped Hex   -- kernel-reducible Array/Vector equality; see HexBasic.ArrayDecEq

public section
set_option backward.proofsInPublic true

/-!
Data carried by modular factorization, lifting, normalization, and factorization results.
-/
namespace Hex

/-- `ZPoly.modP p` never increases the executable dense size: the
coefficientwise reduction maps into a length-`f.size` coefficient list, which
`DensePoly.ofList` then trims of trailing zeros. -/
private theorem size_modP_le (p : Nat) [ZMod64.Bounds p] (f : ZPoly) :
    (ZPoly.modP p f).size ≤ f.size := by
  show (ZPoly.modP p f).coeffs.size ≤ f.size
  unfold ZPoly.modP
  have h := DensePoly.size_ofList_le
    (R := ZMod64 p)
    ((List.range f.size).map
      (fun i => ZMod64.ofNat p (ZPoly.intModNat (f.coeff i) p)))
  have hlen : ((List.range f.size).map
      (fun i => ZMod64.ofNat p (ZPoly.intModNat (f.coeff i) p))).length =
        f.size := by simp
  simpa [DensePoly.size, hlen] using h

/--
Data produced by modular prime selection: the selected prime, the image of the
input polynomial over that prime field, and its modular factors.
-/
structure PrimeChoiceData where
  /-- The selected prime modulus. -/
  p : Nat
  [bounds : ZMod64.Bounds p]
  /-- The input polynomial reduced modulo `p`. -/
  fModP : FpPoly p
  /-- Its monic irreducible factors over the prime field. -/
  factorsModP : Array (FpPoly p)

instance : Inhabited PrimeChoiceData where
  default :=
    { p := 3
      bounds := bounds_three
      fModP := 0
      factorsModP := #[] }

/--
Data produced by Hensel lifting and consumed by integer recombination: the
prime, the requested lift precision, and the lifted integer factors.
-/
structure LiftData where
  /-- The prime underlying the Hensel modulus. -/
  p : Nat
  /-- Positivity of the prime, retained for arithmetic bounds. -/
  p_pos : 0 < p
  /-- The exponent in the lifting modulus `p ^ k`. -/
  k : Nat
  /-- The modular factors lifted to integer polynomials modulo `p ^ k`. -/
  liftedFactors : Array ZPoly

/--
Executable normalization data for the public integer factorization API.

The public input is first split into its integer content, primitive part,
initial `X` power, and primitive square-free part. The Berlekamp-Zassenhaus
prime/lift/factorization computation runs on `squareFreeCore`; the other fields are
reassembled around the resulting factors of the square-free part.
-/
structure FactorNormalizationData where
  /-- The signed-independent integer content of the input. -/
  content : Int
  /-- The content-free input with normalized sign. -/
  primitive : ZPoly
  /-- The largest exponent of `X` dividing the primitive input. -/
  xPower : Nat
  /-- The primitive input after removing its initial power of `X`. -/
  xFreePrimitive : ZPoly
  /-- The primitive product of the distinct nonzero irreducible factors. -/
  squareFreeCore : ZPoly
  /-- The primitive repeated-factor contribution. -/
  repeatedPart : ZPoly

namespace ZPoly

/--
Executable data for the integer scaling transform that sends a primitive
polynomial with positive leading coefficient to a monic integer polynomial with the same roots
(scaled by the leading coefficient).

If `core` has degree `n` and leading coefficient `c`, `monic` is the
coefficientwise integer polynomial `c^(n-1) * core (X / c)`: lower coefficient
`a_i` becomes `a_i * c^(n-1-i)` and the leading coefficient is normalised to
`1`.
-/
structure ToMonicData where
  /-- The primitive positive-leading polynomial being transformed. -/
  core : ZPoly
  /-- The leading coefficient of `core`. -/
  leadingCoeff : Int
  /-- The degree of `core`. -/
  degree : Nat
  /-- The integral monic polynomial obtained by the scaling transform. -/
  monic : ZPoly

namespace ToMonicData

/-- Coefficients of the degree-dependent transformed polynomial. -/
@[expose]
def transformedCoeffs (core : ZPoly) (degree : Nat) : Array Int :=
  ((List.range degree).map fun i =>
      core.coeff i * (DensePoly.leadingCoeff core) ^ (degree - 1 - i)).toArray.push 1

/-- The degree-dependent transform used for repeated-factor recovery. -/
@[expose]
def transformedCore (core : ZPoly) (degree : Nat) : ZPoly :=
  { coeffs := transformedCoeffs core degree
    normalized := by
      right
      change (transformedCoeffs core degree).back? ≠ some (0 : Int)
      simp [transformedCoeffs] }

@[simp, grind =] theorem transformedCoeffs_size (core : ZPoly) (degree : Nat) :
    (transformedCoeffs core degree).size = degree + 1 := by
  simp [transformedCoeffs]

@[simp] theorem transformedCoeffs_getD_top (core : ZPoly) (degree : Nat) :
    (transformedCoeffs core degree).getD degree 0 = 1 := by
  simp [transformedCoeffs]

@[simp, grind =] theorem transformedCore_size (core : ZPoly) (degree : Nat) :
    (transformedCore core degree).size = degree + 1 := by
  simp [transformedCore, DensePoly.size]

/-- The coefficient in the prescribed top degree of the transformed polynomial is one. -/
theorem transformedCore_coeff_top (core : ZPoly) (degree : Nat) :
    (transformedCore core degree).coeff degree = 1 := by
  change (transformedCoeffs core degree).getD degree (0 : Int) = 1
  exact transformedCoeffs_getD_top core degree

theorem transformedCore_monic (core : ZPoly) (degree : Nat) :
    DensePoly.Monic (transformedCore core degree) := by
  unfold DensePoly.Monic DensePoly.leadingCoeff transformedCore
  simp [transformedCoeffs]

@[simp, grind =] theorem transformedCore_degree_getD (core : ZPoly) (degree : Nat) :
    (transformedCore core degree).degree?.getD 0 = degree := by
  unfold DensePoly.degree? transformedCore DensePoly.size
  simp [transformedCoeffs]

end ToMonicData

/-- Build the `ToMonicData` packet for a square-free part by the integer scaling transform. -/
@[expose]
def toMonic (core : ZPoly) : ToMonicData :=
  let degree := core.degree?.getD 0
  { core
    leadingCoeff := DensePoly.leadingCoeff core
    degree
    monic :=
      if DensePoly.leadingCoeff core = 1 then
        core
      else
        ToMonicData.transformedCore core degree }

@[simp, grind =] theorem toMonic_core (core : ZPoly) :
    (toMonic core).core = core := rfl

@[simp, grind =] theorem toMonic_leadingCoeff (core : ZPoly) :
    (toMonic core).leadingCoeff = DensePoly.leadingCoeff core := rfl

@[simp, grind =] theorem toMonic_degree (core : ZPoly) :
    (toMonic core).degree = core.degree?.getD 0 := rfl

/-- The polynomial stored by `toMonic` is monic, including the degenerate
constant branches. -/
theorem toMonic_monic_isMonic (core : ZPoly) :
    DensePoly.Monic (toMonic core).monic := by
  unfold toMonic
  by_cases hmonic : DensePoly.leadingCoeff core = 1
  · simp [hmonic, DensePoly.Monic]
  · simp [hmonic, ToMonicData.transformedCore_monic]

/-- The `monic` field of `toMonic core` is monic once the source has positive
degree. -/
theorem toMonic_monic_isMonic_of_pos_degree
    (core : ZPoly) (_hpos_lc : 0 < DensePoly.leadingCoeff core)
    (_hdegree : 0 < (toMonic core).degree) :
    DensePoly.Monic (toMonic core).monic :=
  toMonic_monic_isMonic core

/-- The `monic` field preserves the recorded degree in nonconstant cases. -/
theorem toMonic_monic_degree_eq_of_pos_degree
    (core : ZPoly) (_hpos_lc : 0 < DensePoly.leadingCoeff core)
    (_hdegree : 0 < (toMonic core).degree) :
    (toMonic core).monic.degree?.getD 0 = (toMonic core).degree := by
  unfold toMonic
  by_cases hmonic : DensePoly.leadingCoeff core = 1
  · simp [hmonic]
  · simp [hmonic]

/-- Applying `toMonic` to an already-monic polynomial leaves its `monic` field equal
to the original. -/
theorem toMonic_monic_eq_core_of_leadingCoeff_eq_one
    (core : ZPoly) (hmonic : DensePoly.leadingCoeff core = 1) :
    (toMonic core).monic = core := by
  simp [toMonic, hmonic]

private def toMonicGuardMonic : ToMonicData :=
  toMonic (DensePoly.ofCoeffs #[1, 3, 1])

#guard toMonicGuardMonic.monic = toMonicGuardMonic.core

private def toMonicGuardQuadratic : ToMonicData :=
  toMonic (DensePoly.ofCoeffs #[1, 3, 2])

#guard toMonicGuardQuadratic.degree = 2
#guard toMonicGuardQuadratic.leadingCoeff = 2
#guard toMonicGuardQuadratic.monic = DensePoly.ofCoeffs #[2, 3, 1]

private def toMonicGuardZero : ToMonicData :=
  toMonic 0

#guard toMonicGuardZero.degree = 0
#guard toMonicGuardZero.monic = DensePoly.ofCoeffs #[1]

end ZPoly

/--
Public factorization result for an integer polynomial {name}`Hex.ZPoly`.

The scalar carries the input's signed content: for nonzero inputs this is
`sign(lc f) * ZPoly.content f`, while zero inputs use scalar `0`. Polynomial
factors are primitive, positive-leading-coefficient factors stored with
explicit multiplicities; factor order remains operational, with the
mathematical contract expressed by multiplying the scalar and stored factors.
-/
structure Factorization where
  /-- Signed scalar absorbing both sign and integer content. -/
  scalar : Int
  /-- Polynomial factors paired with explicit positive multiplicities. -/
  factors : Array (ZPoly × Nat)
deriving DecidableEq

namespace Factorization

/-- Natural powers of an integer polynomial. -/
@[expose]
def polyPow (f : ZPoly) : Nat → ZPoly
  | 0 => 1
  | n + 1 => polyPow f n * f

/-- Public wrapper for the polynomial power used by `Factorization.product`. -/
@[expose]
def factorPower (f : ZPoly) (n : Nat) : ZPoly :=
  polyPow f n

@[simp, grind =] theorem factorPower_zero (f : ZPoly) :
    factorPower f 0 = (1 : ZPoly) := rfl

@[simp, grind =] theorem factorPower_succ (f : ZPoly) (n : Nat) :
    factorPower f (n + 1) = factorPower f n * f := rfl

/-- Expand multiplicity pairs into the ordered polynomial product. -/
@[expose]
def product (φ : Factorization) : ZPoly :=
  φ.factors.foldl (fun acc factor => acc * polyPow factor.1 factor.2) (DensePoly.C φ.scalar)

@[simp, grind =] theorem product_mk_empty (scalar : Int) :
    product { scalar := scalar, factors := #[] } = DensePoly.C scalar := rfl

/--
Characterize `product` using the public `factorPower` wrapper instead of the
private recursion used internally.
-/
theorem product_eq_foldl_factorPower (φ : Factorization) :
    φ.product =
      φ.factors.foldl
        (fun acc factor => acc * factorPower factor.1 factor.2)
        (DensePoly.C φ.scalar) := by
  rfl

end Factorization

/-- Compute the normalization data required before the square-free computation. -/
@[expose]
def normalizeForFactor (f : ZPoly) : FactorNormalizationData :=
  let primitive := ZPoly.primitivePart f
  let xData := ZPoly.extractXPower primitive
  let sqData := ZPoly.primitiveSquareFreeDecomposition xData.core
  { content := ZPoly.content f
    primitive
    xPower := xData.power
    xFreePrimitive := xData.core
    squareFreeCore := sqData.squareFreeCore
    repeatedPart := sqData.repeatedPart }

/-- Compute an integer polynomial's content and primitive part together.  The
logical surface is the ordinary pair of operations. -/
@[expose]
def ZPoly.contentPrimitive (f : ZPoly) : Int × ZPoly :=
  (ZPoly.content f, ZPoly.primitivePart f)

/-- One-pass runtime implementation of {name}`ZPoly.contentPrimitive`: compute
the coefficient gcd once, then reuse it for both the content and coefficient
division. -/
@[expose]
def ZPoly.contentPrimitiveImpl (f : ZPoly) : Int × ZPoly :=
  let cNat := DensePoly.contentNatImpl f
  let primitive :=
    if cNat = 0 then
      0
    else
      let c := Int.ofNat cNat
      DensePoly.ofCoeffs (f.toArray.map (fun coeff => coeff / c))
  (Int.ofNat cNat, primitive)

theorem ZPoly.contentPrimitive_eq_impl_value (f : ZPoly) :
    ZPoly.contentPrimitive f = ZPoly.contentPrimitiveImpl f := by
  unfold ZPoly.contentPrimitive ZPoly.contentPrimitiveImpl ZPoly.content
    ZPoly.primitivePart
  rw [DensePoly.primitivePart_eq_primitivePartImpl]
  unfold DensePoly.content DensePoly.primitivePartImpl
  rw [DensePoly.contentNat_eq_contentNatImpl]

@[csimp]
theorem ZPoly.contentPrimitive_eq_impl :
    @ZPoly.contentPrimitive = @ZPoly.contentPrimitiveImpl := by
  funext f
  exact ZPoly.contentPrimitive_eq_impl_value f

/-- Certified trial prime for the modular square-free fast path.  `499` is a
cheap fixed choice: it is large enough that a distinct-root input rarely reduces
non-square-free at it, but it carries no guarantee (a rationally square-free
input whose discriminant is divisible by `499` reduces non-square-free and simply
takes the exact fallback -- never a wrong answer). -/
theorem prime_499 : Hex.Nat.Prime 499 :=
  Hex.Nat.isPrimeTrial_isPrime (by decide)

instance bounds_499 : ZMod64.Bounds 499 := ⟨by decide, by decide⟩

/-- The prepared-input form of the modular square-free trial. -/
@[expose]
def modularSquareFreeCoreFires (q : ZPoly) : Bool :=
  !q.isZero && (ZPoly.leadingCoeffModP q 499 != 0) && ZPoly.separableModP q 499

/-- Boolean guard for the modular square-free fast path: the primitive `x`-free
square-free part is nonzero, admissible at the trial prime, and separable over `𝔽_p`. -/
@[expose]
def modularSquareFreeFires (f : ZPoly) : Bool :=
  let q := ZPoly.primitivePart (ZPoly.extractXPower (ZPoly.primitivePart f)).core
  modularSquareFreeCoreFires q

/-- Fast implementation of `normalizeForFactor`: a machine-word `𝔽_p`
square-freeness trial on the primitive `x`-free square-free part.  When it fires (the input
is square-free over `ℚ`) the decomposition is trivial; otherwise it falls back to
the exact rational computation, inlined rather than a self-call so the `@[csimp]`
rewrite below does not make the fallback recurse.  Proven equal to
`normalizeForFactor`. -/
@[expose]
def normalizeForFactorFast (f : ZPoly) : FactorNormalizationData :=
  let contentPrimitive := ZPoly.contentPrimitive f
  let primitive := contentPrimitive.2
  let xData := ZPoly.extractXPower primitive
  let squareFreeCore := ZPoly.primitivePart xData.core
  if modularSquareFreeCoreFires squareFreeCore then
    { content := contentPrimitive.1
      primitive
      xPower := xData.power
      xFreePrimitive := xData.core
      squareFreeCore := ZPoly.normalizePrimitiveSign squareFreeCore
      repeatedPart := 1 }
  else
    let sqData := ZPoly.primitiveSquareFreeDecomposition xData.core
    { content := contentPrimitive.1
      primitive
      xPower := xData.power
      xFreePrimitive := xData.core
      squareFreeCore := sqData.squareFreeCore
      repeatedPart := sqData.repeatedPart }

@[csimp]
theorem normalizeForFactor_eq_normalizeForFactorFast :
    normalizeForFactor = normalizeForFactorFast := by
  funext f
  simp only [normalizeForFactor, normalizeForFactorFast, ZPoly.contentPrimitive]
  by_cases hcond : modularSquareFreeFires f = true
  · have hcond' : modularSquareFreeCoreFires
        (ZPoly.primitivePart (ZPoly.extractXPower (ZPoly.primitivePart f)).core) = true := by
      simpa [modularSquareFreeFires] using hcond
    rw [if_pos hcond']
    simp only [modularSquareFreeFires, modularSquareFreeCoreFires,
      Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne] at hcond
    obtain ⟨⟨hq_isZero, hadm⟩, hsep⟩ := hcond
    have hq_ne : ZPoly.primitivePart (ZPoly.extractXPower (ZPoly.primitivePart f)).core ≠ 0 := by
      intro h
      have hpos := (DensePoly.isZero_eq_false_iff _).1 hq_isZero
      rw [h, DensePoly.size_zero] at hpos
      omega
    have hcore_ne : (ZPoly.extractXPower (ZPoly.primitivePart f)).core ≠ 0 := by
      intro h
      apply hq_ne
      change ZPoly.primitivePart (ZPoly.extractXPower (ZPoly.primitivePart f)).core = 0
      rw [h]
      exact DensePoly.primitivePart_eq_zero_of_content_eq_zero 0 DensePoly.content_zero
    have hsq : ZPoly.SquareFreeRat
        (ZPoly.primitivePart (ZPoly.extractXPower (ZPoly.primitivePart f)).core) :=
      ZPoly.squareFreeRat_of_separableModP _ 499 prime_499 hadm hsep
    rw [ZPoly.primitiveSquareFreeDecomposition_squareFreeCore_eq_of_squareFreeRat _ hcore_ne hsq,
        ZPoly.primitiveSquareFreeDecomposition_repeatedPart_eq_one_of_squareFreeRat _ hcore_ne hsq]
  · have hcond' : modularSquareFreeCoreFires
        (ZPoly.primitivePart (ZPoly.extractXPower (ZPoly.primitivePart f)).core) ≠ true := by
      simpa [modularSquareFreeFires] using hcond
    rw [if_neg hcond']

private def contentFactorArray (content : Int) : Array ZPoly :=
  if content = 1 then
    #[]
  else
    #[DensePoly.C content]

/-- The factor `X` with the requested multiplicity, omitted at multiplicity zero. -/
@[expose]
def xPowerFactorArray (power : Nat) : Array ZPoly :=
  (List.replicate power ZPoly.X).toArray

/-- The repeated part as a singleton factor array, omitting the unit polynomial. -/
@[expose]
def repeatedPartFactorArray (repeatedPart : ZPoly) : Array ZPoly :=
  if repeatedPart = 1 then
    #[]
  else
    #[repeatedPart]

/-- The signed content carried by the scalar part of a factorization. -/
@[expose]
def signedContentScalar (f : ZPoly) : Int :=
  if f = 0 then
    0
  else if DensePoly.leadingCoeff f < 0 then
    -ZPoly.content f
  else
    ZPoly.content f

/-- Normalize a polynomial factor's sign by negating it whenever the leading
coefficient is negative.  The result has nonnegative leading coefficient and is
associated to the input over `ℤ`. -/
@[expose]
def normalizeFactorSign (f : ZPoly) : ZPoly :=
  if DensePoly.leadingCoeff f < 0 then
    DensePoly.scale (-1 : Int) f
  else
    f

/-- A polynomial factor is recorded by the factorization routines only
when it is not zero and not a unit (`±1`).  Exposed publicly so that
Mathlib-side lemmas can transport the predicate into `¬ IsUnit` over
`Polynomial ℤ`. -/
@[expose]
def shouldRecordPolynomialFactor (f : ZPoly) : Bool :=
  f ≠ 0 && f ≠ 1 && f ≠ DensePoly.C (-1)

/-- Increase the multiplicity of `f`, or append it with multiplicity one. -/
@[expose]
def bumpFactorMultiplicity (f : ZPoly) : List (ZPoly × Nat) → List (ZPoly × Nat)
  | [] => [(f, 1)]
  | entry :: entries =>
      if entry.1 = f then
        (entry.1, entry.2 + 1) :: entries
      else
        entry :: bumpFactorMultiplicity f entries

/-- Collect equal factors and their multiplicities in first-occurrence order. -/
@[expose]
def collectFactorMultiplicities (factors : Array ZPoly) : Array (ZPoly × Nat) :=
  factors.toList.foldl
    (fun acc factor =>
      let factor := normalizeFactorSign factor
      if shouldRecordPolynomialFactor factor then
        bumpFactorMultiplicity factor acc
      else
        acc)
    []
  |>.reverse.toArray

/-- The `X`-power and repeated-part factors preceding the square-free factors. -/
@[expose]
def polynomialNormalizationPrefixFactors (d : FactorNormalizationData) : Array ZPoly :=
  xPowerFactorArray d.xPower ++ repeatedPartFactorArray d.repeatedPart

/-- Factors that come from normalization before the primitive square-free part is factored. -/
def normalizationPrefixFactors (d : FactorNormalizationData) : Array ZPoly :=
  contentFactorArray d.content ++
    xPowerFactorArray d.xPower ++
    repeatedPartFactorArray d.repeatedPart

/-- Reassemble normalization factors around the factors of the primitive square-free part. -/
def reassembleNormalizedFactors
    (d : FactorNormalizationData) (coreFactors : Array ZPoly) : Array ZPoly :=
  normalizationPrefixFactors d ++ coreFactors

/--
Exact-division check on integer polynomials: returns the quotient when
`quot * candidate = target` exactly, and rejects unit candidates so iterated
calls cannot loop forever on `±1`.
-/
@[expose]
def exactQuotient? (target candidate : ZPoly) : Option ZPoly :=
  if candidate.isZero || candidate = 1 then
    none
  else
    let qr := DensePoly.divMod target candidate
    if qr.2 = 0 && qr.1 * candidate == target then
      some qr.1
    else
      none

/-- Successful exact-division extracts a multiplication witness:
`exactQuotient? target candidate = some quotient` implies
`quotient * candidate = target`. Forward companion of
`exactQuotient?_eq_some_of_mul_eq_monic_of_pos_degree`. -/
theorem exactQuotient?_product
    {target candidate quotient : ZPoly}
    (hquot : exactQuotient? target candidate = some quotient) :
    quotient * candidate = target := by
  unfold exactQuotient? at hquot
  split at hquot
  · contradiction
  · rename_i hnontrivial
    generalize hqr : DensePoly.divMod target candidate = qr at hquot
    cases qr with
    | mk q r =>
        simp only at hquot
        split at hquot
        · rename_i hcheck
          cases hquot
          exact (by
            simpa [Bool.and_eq_true, beq_iff_eq] using hcheck : r = 0 ∧ quotient * candidate = target).2
        · contradiction

/--
Greedy peel of `candidate^?` out of `target` via repeated exact division.
Returns `(residual, multiplicity)` with the invariant
`candidate ^ multiplicity * residual = target`. The recursion is bounded by
`fuel`, which the caller chooses based on the source degree.
-/
@[expose]
def consumeExactPower (target candidate : ZPoly) : Nat → ZPoly × Nat
  | 0 => (target, 0)
  | fuel + 1 =>
      match exactQuotient? target candidate with
      | some quot =>
          let (residual, m) := consumeExactPower quot candidate fuel
          (residual, m + 1)
      | none => (target, 0)

/--
Fold `consumeExactPower` over a list of candidate factors, accumulating
emitted copies and tracking the residual that has not yet been factored.
Invariant: `polyProduct emitted * residual = initialRepeatedPart`.
-/
@[expose]
def expandRepeatedPartFactorsAux : List ZPoly → ZPoly → Nat → Array ZPoly × ZPoly
  | [], rp, _ => (#[], rp)
  | q :: qs, rp, fuel =>
      let (rp', m) := consumeExactPower rp q fuel
      let (rest, residual) := expandRepeatedPartFactorsAux qs rp' fuel
      ((List.replicate m q).toArray ++ rest, residual)

/--
Compute `(emitted, residual)` where each candidate factor `q` from
`coreFactors` appears in `emitted` to the maximum multiplicity such that
`q^k` exactly divides the running repeated-part. The fuel is the source
size, which dominates any irreducible's multiplicity in `repeatedPart`.
-/
@[expose]
def expandRepeatedPartFactorArray (rp : ZPoly) (coreFactors : Array ZPoly) :
    Array ZPoly × ZPoly :=
  expandRepeatedPartFactorsAux coreFactors.toList rp (rp.size + 1)

end Hex
