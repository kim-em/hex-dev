import HexPoly.Euclid

/-!
Core conformance checks for `hex-poly`'s dense/basic and Euclidean-operation surface.

Oracle: none
Mode: always
Covered operations:
- dense representation constructors and accessors (`ofCoeffs`, `ofList`, `C`, `monomial`, `size`, `isZero`, `coeff`, `degree?`, `support`, `toArray`)
- basic executable arithmetic (`scale`, `shift`, `add`, `sub`, `mul`, `eval`, `compose`, `derivative`)
- Euclidean helpers (`leadingCoeff`, `divModMonic`, `divMod`, `/`, `%`, `modByMonic`, `gcd`, `xgcd`)
- integer content helpers (`content`, `primitivePart`)
- polynomial CRT witness construction (`polyCRT`)
Covered properties:
- normalization removes trailing zeros from committed raw coefficient inputs
- dense structural equality matches additive identity and commutativity checks on committed fixtures
- scaling by zero and shifting zero collapse back to the normalized zero polynomial
- multiplication by the constant polynomial `1` preserves committed inputs
- Horner evaluation, polynomial composition, and formal derivative agree with committed
  small polynomial calculations
- division fixtures satisfy `quotient * divisor + remainder = dividend`, including exact,
  zero-dividend, and fractional-quotient cases
- `gcd` and `xgcd` agree on committed fixtures and the returned Bezout coefficients
  reconstruct the gcd
- `content` times `primitivePart` reconstructs committed integer polynomials
- `polyCRT` witnesses reduce to both prescribed residues modulo committed coprime monic factors
Covered edge cases:
- the zero polynomial encoded with all-zero trailing coefficients
- sparse polynomials with internal zeros but nonzero leading terms
- shifted and scaled monomials that exercise normalization after arithmetic
- evaluation, composition, and differentiation of zero, constant, and sparse inputs
- Euclidean division with zero dividend, exact division, and non-monic divisors with
  fractional quotients
- integer content for zero, already primitive, and nontrivial-content polynomials
- CRT residues for degree-zero inputs modulo coprime degree-12 moduli
-/

namespace Hex

namespace DensePoly

-- Typical fixture: `polyTypical = 3 - 2x^2 + x^12`, exercising the upper end of the
-- `core` profile's polynomial-degree band (SPEC/testing.md § "Profile sizes").
private def coeffsTypical : Array Int := #[3, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
-- Edge fixture: zero polynomial encoded with trailing zeros.
private def coeffsEdge : Array Int := #[0, 0, 0]
-- Adversarial fixture: `4x - 5x^3 + 6x^12`, sparse with internal zeros and three
-- trailing zeros that normalization must strip.
private def coeffsAdversarial : Array Int := #[0, 4, 0, -5, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0]

private def polyTypical : DensePoly Int := ofCoeffs coeffsTypical
private def polyEdge : DensePoly Int := ofCoeffs coeffsEdge
private def polyAdversarial : DensePoly Int := ofCoeffs coeffsAdversarial

-- Smaller second operand for binary arithmetic so multiplication outputs stay in
-- a hand-tractable degree band.
private def listTypical : List Int := [-1, 5, 2, 0]
private def listEdge : List Int := [0, 0]
private def listAdversarial : List Int := [0, 7, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0]

private def polyFromListTypical : DensePoly Int := ofList listTypical
private def polyFromListEdge : DensePoly Int := ofList listEdge
private def polyFromListAdversarial : DensePoly Int := ofList listAdversarial

private def constTypical : DensePoly Int := C 5
private def constEdge : DensePoly Int := C 0
private def constAdversarial : DensePoly Int := C (-9)

private def monomialTypical : DensePoly Int := monomial 11 3
private def monomialEdge : DensePoly Int := monomial 12 0
private def monomialAdversarial : DensePoly Int := monomial 12 (-2)

-- Typical division: `(x^12 - 1) = (x - 1) * (x^11 + x^10 + ... + 1) + 0`. The quotient
-- is the well-known telescoping factorisation `(x^k - 1) / (x - 1) = sum_{i=0}^{k-1} x^i`.
private def ratDivTypicalDividend : DensePoly Rat :=
  ofCoeffs #[-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
private def ratDivTypicalDivisor : DensePoly Rat := ofCoeffs #[-1, 1]
private def ratDivTypicalQuotient : DensePoly Rat :=
  ofCoeffs #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
private def ratDivTypicalRemainder : DensePoly Rat := 0

private def ratDivEdgeDividend : DensePoly Rat := 0
private def ratDivEdgeDivisor : DensePoly Rat := ofCoeffs #[1, 1]
private def ratDivEdgeQuotient : DensePoly Rat := 0
private def ratDivEdgeRemainder : DensePoly Rat := 0

-- Adversarial division: dividend constructed from `(2x + 1) * (-2 + 3x^5 + x^11) + 7/2`
-- = `3/2 - 4x + 3x^5 + 6x^6 + x^11 + 2x^12`. Non-monic divisor forces a fractional
-- remainder.
private def ratDivAdversarialDividend : DensePoly Rat :=
  ofCoeffs #[3 / 2, -4, 0, 0, 0, 3, 6, 0, 0, 0, 0, 1, 2]
private def ratDivAdversarialDivisor : DensePoly Rat := ofCoeffs #[1, 2]
private def ratDivAdversarialQuotient : DensePoly Rat :=
  ofCoeffs #[-2, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 1]
private def ratDivAdversarialRemainder : DensePoly Rat := ofCoeffs #[7 / 2]

-- Typical gcd: `Left = (x - 1)(x^11 + 1)`, `Right = (x - 1)(x^11 - 1)`. Both are monic
-- of equal degree, so the first Euclidean step has quotient `1` and remainder
-- `Left - Right = 2x - 2 = 2(x - 1)`. The second step divides `Right` by `2(x - 1)`
-- exactly (since `(x - 1) | Right`), terminating with `gcd = 2x - 2`.
private def ratGcdTypicalLeft : DensePoly Rat :=
  ofCoeffs #[-1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1]
private def ratGcdTypicalRight : DensePoly Rat :=
  ofCoeffs #[1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1]
private def ratGcdTypicalValue : DensePoly Rat := ofCoeffs #[-2, 2]

private def ratGcdEdgeLeft : DensePoly Rat := 0
private def ratGcdEdgeRight : DensePoly Rat := ofCoeffs #[2, 1]

-- Adversarial gcd: `Left = (x^4 + 1) * (x^8 + 2x^3 + 5)`, `Right = x^4 + 1`. Right divides
-- Left, so the Euclidean algorithm returns `gcd = Right` after a single divMod step.
private def ratGcdAdversarialLeft : DensePoly Rat :=
  ofCoeffs #[5, 0, 0, 2, 5, 0, 0, 2, 1, 0, 0, 0, 1]
private def ratGcdAdversarialRight : DensePoly Rat := ofCoeffs #[1, 0, 0, 0, 1]

private def intContentZero : DensePoly Int := ofCoeffs #[0, 0, 0]
-- Primitive degree-12 polynomial: gcd of nonzero coefficients `{1, 5, -2, 3}` is 1
-- (because 1 is in the set).
private def intContentPrimitive : DensePoly Int :=
  ofCoeffs #[1, 0, 0, 5, 0, 0, 0, -2, 0, 0, 0, 0, 3]
-- `intContentNontrivial = 6 * intContentPrimitive`; content = 6, primitive part = the above.
private def intContentNontrivial : DensePoly Int :=
  ofCoeffs #[6, 0, 0, 30, 0, 0, 0, -12, 0, 0, 0, 0, 18]

-- Coprime degree-12 moduli: `(1 + x^12) - (x^12 - 1) = 2`, so the Bezout identity
-- `(1/2)(1 + x^12) + (-1/2)(x^12 - 1) = 1` holds. Witness derived from
-- `polyCRT a b u v s t = u*t*b + v*s*a`:
--   `5 * (-1/2) * (x^12 - 1) + 7 * (1/2) * (1 + x^12)`
--   `= (-5/2)(x^12 - 1) + (7/2)(1 + x^12)`
--   `= (5/2 + 7/2) + (-5/2 + 7/2) x^12 = 6 + x^12`.
private def crtModA : DensePoly Rat :=
  ofCoeffs #[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
private def crtModB : DensePoly Rat :=
  ofCoeffs #[-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
private def crtResidueA : DensePoly Rat := C 5
private def crtResidueB : DensePoly Rat := C 7
private def crtBezoutS : DensePoly Rat := C (1 / 2)
private def crtBezoutT : DensePoly Rat := C (-1 / 2)
private def crtWitness : DensePoly Rat :=
  polyCRT crtModA crtModB crtResidueA crtResidueB crtBezoutS crtBezoutT

-- `#eval` refuses to reduce `DensePoly` values because `ofCoeffs` and `monomial`
-- still carry sorry-backed normalization proofs in their propositional fields.
/-- info: [3, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] -/
#guard_msgs in #eval! polyTypical.toArray.toList

/-- info: [] -/
#guard_msgs in #eval! polyEdge.toArray.toList

/-- info: [0, 4, 0, -5, 0, 0, 0, 0, 0, 0, 0, 0, 6] -/
#guard_msgs in #eval! polyAdversarial.toArray.toList

#guard polyTypical = ofCoeffs #[3, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
#guard polyEdge = (0 : DensePoly Int)
#guard polyAdversarial.support = [1, 3, 12]

#guard polyFromListTypical.toArray.toList = [-1, 5, 2]
#guard polyFromListEdge = (0 : DensePoly Int)
#guard polyFromListAdversarial.toArray.toList = [0, 7, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 8]

#guard constTypical.toArray.toList = [5]
#guard constEdge = (0 : DensePoly Int)
#guard constAdversarial.toArray.toList = [-9]

#guard monomialTypical.toArray.toList = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3]
#guard monomialEdge = (0 : DensePoly Int)
#guard monomialAdversarial.toArray.toList = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2]

#guard polyTypical.size = 13
#guard polyEdge.size = 0
#guard polyAdversarial.size = 13

#guard !polyTypical.isZero
#guard polyEdge.isZero
#guard !monomialAdversarial.isZero

#guard polyTypical.coeff 2 = -2
#guard polyEdge.coeff 0 = 0
#guard polyAdversarial.coeff 5 = 0

#guard polyTypical.degree? = some 12
#guard polyEdge.degree? = none
#guard monomialAdversarial.degree? = some 12

#guard polyTypical.support = [0, 2, 12]
#guard polyEdge.support = []
#guard polyAdversarial.support = [1, 3, 12]

#guard polyTypical.toArray.toList = [3, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
#guard polyEdge.toArray.toList = []
#guard monomialAdversarial.toArray.toList = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2]

/-- info: [9, 0, -6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3] -/
#guard_msgs in #eval! (scale 3 polyTypical).toArray.toList

#guard scale 0 polyAdversarial = (0 : DensePoly Int)
#guard (scale (-2) monomialAdversarial).toArray.toList =
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4]

/-- info: [0, 0, 3, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] -/
#guard_msgs in #eval! (shift 2 polyTypical).toArray.toList

#guard shift 0 polyEdge = (0 : DensePoly Int)
#guard (shift 1 monomialAdversarial).toArray.toList =
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2]

/-- info: [2, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] -/
#guard_msgs in #eval! (polyTypical + polyFromListTypical).toArray.toList

#guard polyEdge + constEdge = (0 : DensePoly Int)
#guard (polyAdversarial + monomialAdversarial).toArray.toList =
  [0, 4, 0, -5, 0, 0, 0, 0, 0, 0, 0, 0, 4]
#guard polyTypical + (0 : DensePoly Int) = polyTypical
#guard polyTypical + polyFromListTypical = polyFromListTypical + polyTypical

/-- info: [4, -5, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] -/
#guard_msgs in #eval! (polyTypical - polyFromListTypical).toArray.toList

#guard polyEdge - constEdge = (0 : DensePoly Int)
#guard (polyAdversarial - monomialAdversarial).toArray.toList =
  [0, 4, 0, -5, 0, 0, 0, 0, 0, 0, 0, 0, 8]

/-- info: [-3, 15, 8, -10, -4, 0, 0, 0, 0, 0, 0, 0, -1, 5, 2] -/
#guard_msgs in #eval! (polyTypical * polyFromListTypical).toArray.toList

#guard polyEdge * constEdge = (0 : DensePoly Int)
#guard (polyAdversarial * monomialAdversarial).toArray.toList =
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, -12]
#guard polyTypical * C 1 = polyTypical

-- `eval polyTypical 2 = 3 - 2*4 + 4096 = 4091`.
#guard eval polyTypical 2 = 4091
#guard eval polyEdge 7 = 0
-- `eval polyAdversarial (-1) = 4*(-1) - 5*(-1) + 6*1 = -4 + 5 + 6 = 7`.
#guard eval polyAdversarial (-1) = 7

/-- info: [4091] -/
#guard_msgs in #eval! (compose polyTypical (C 2)).toArray.toList

#guard compose polyEdge polyTypical = (0 : DensePoly Int)
-- Substituting `x ↦ -x` into `4x - 5x^3 + 6x^12` flips the odd-degree signs.
#guard (compose polyAdversarial (monomial 1 (-1))).toArray.toList =
  [0, -4, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 6]

/-- info: [0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12] -/
#guard_msgs in #eval! (derivative polyTypical).toArray.toList

#guard derivative polyEdge = (0 : DensePoly Int)
-- Derivative of `4x - 5x^3 + 6x^12` is `4 - 15x^2 + 72x^11`.
#guard (derivative polyAdversarial).toArray.toList =
  [4, 0, -15, 0, 0, 0, 0, 0, 0, 0, 0, 72]

#guard ratDivTypicalDividend.leadingCoeff = 1
#guard ratDivEdgeDividend.leadingCoeff = 0
#guard ratDivAdversarialDividend.leadingCoeff = 2

#guard divModMonic ratDivTypicalDividend ratDivTypicalDivisor (by rfl) =
  (ratDivTypicalQuotient, ratDivTypicalRemainder)
#guard divModMonic ratDivEdgeDividend ratDivEdgeDivisor (by rfl) =
  (ratDivEdgeQuotient, ratDivEdgeRemainder)
-- `(x - 1) | (x - 1)(x^11 + 1)`, with quotient `x^11 + 1`.
#guard divModMonic ratGcdTypicalLeft ratDivTypicalDivisor (by rfl) =
  (ofCoeffs #[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0)

#guard divMod ratDivTypicalDividend ratDivTypicalDivisor =
  (ratDivTypicalQuotient, ratDivTypicalRemainder)
#guard divMod ratDivEdgeDividend ratDivEdgeDivisor =
  (ratDivEdgeQuotient, ratDivEdgeRemainder)
#guard divMod ratDivAdversarialDividend ratDivAdversarialDivisor =
  (ratDivAdversarialQuotient, ratDivAdversarialRemainder)

#guard ratDivTypicalDividend / ratDivTypicalDivisor = ratDivTypicalQuotient
#guard ratDivEdgeDividend / ratDivEdgeDivisor = ratDivEdgeQuotient
#guard ratDivAdversarialDividend / ratDivAdversarialDivisor = ratDivAdversarialQuotient

#guard ratDivTypicalDividend % ratDivTypicalDivisor = ratDivTypicalRemainder
#guard ratDivEdgeDividend % ratDivEdgeDivisor = ratDivEdgeRemainder
#guard ratDivAdversarialDividend % ratDivAdversarialDivisor = ratDivAdversarialRemainder

#guard modByMonic ratDivTypicalDividend ratDivTypicalDivisor (by rfl) =
  ratDivTypicalRemainder
#guard modByMonic ratDivEdgeDividend ratDivEdgeDivisor (by rfl) =
  ratDivEdgeRemainder
#guard modByMonic ratGcdTypicalLeft ratDivTypicalDivisor (by rfl) = 0

#guard ratDivTypicalQuotient * ratDivTypicalDivisor + ratDivTypicalRemainder =
  ratDivTypicalDividend
#guard ratDivEdgeQuotient * ratDivEdgeDivisor + ratDivEdgeRemainder =
  ratDivEdgeDividend
#guard ratDivAdversarialQuotient * ratDivAdversarialDivisor + ratDivAdversarialRemainder =
  ratDivAdversarialDividend

#guard gcd ratGcdTypicalLeft ratGcdTypicalRight = ratGcdTypicalValue
#guard gcd ratGcdEdgeLeft ratGcdEdgeRight = ratGcdEdgeRight
#guard gcd ratGcdAdversarialLeft ratGcdAdversarialRight = ratGcdAdversarialRight

#guard (xgcd ratGcdTypicalLeft ratGcdTypicalRight).gcd = ratGcdTypicalValue
#guard (xgcd ratGcdEdgeLeft ratGcdEdgeRight).gcd = ratGcdEdgeRight
#guard (xgcd ratGcdAdversarialLeft ratGcdAdversarialRight).gcd = ratGcdAdversarialRight

#guard
  let r := xgcd ratGcdTypicalLeft ratGcdTypicalRight
  r.left * ratGcdTypicalLeft + r.right * ratGcdTypicalRight = r.gcd
#guard
  let r := xgcd ratGcdEdgeLeft ratGcdEdgeRight
  r.left * ratGcdEdgeLeft + r.right * ratGcdEdgeRight = r.gcd
#guard
  let r := xgcd ratGcdAdversarialLeft ratGcdAdversarialRight
  r.left * ratGcdAdversarialLeft + r.right * ratGcdAdversarialRight = r.gcd

#guard content intContentZero = 0
#guard content intContentPrimitive = 1
#guard content intContentNontrivial = 6

#guard primitivePart intContentZero = 0
#guard primitivePart intContentPrimitive = intContentPrimitive
#guard primitivePart intContentNontrivial = intContentPrimitive

#guard scale (content intContentZero) (primitivePart intContentZero) = intContentZero
#guard scale (content intContentPrimitive) (primitivePart intContentPrimitive) =
  intContentPrimitive
#guard scale (content intContentNontrivial) (primitivePart intContentNontrivial) =
  intContentNontrivial

#guard crtBezoutS * crtModA + crtBezoutT * crtModB = 1
#guard crtWitness = ofCoeffs #[6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
#guard crtWitness % crtModA = crtResidueA % crtModA
#guard crtWitness % crtModB = crtResidueB % crtModB

end DensePoly

end Hex
