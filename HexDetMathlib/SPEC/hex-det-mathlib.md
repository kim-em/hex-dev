# hex-det-mathlib

Correctness of [hex-det](../../HexDet/SPEC/hex-det.md)'s dispatch and correspondence with
Mathlib's determinant. This is a `correspondence-only-layer`, registered
with `correspondence_only: true`. It owns no runtime determinant, conformance
driver, benchmark process, or tactic.

Computational conformance owner: `HexDet`.

Computational performance owner: `HexDet`.

## Dependencies

Direct dependencies are `HexDet`, `HexBareissMathlib`,
`HexCharPolyMathlib`, `HexDeterminantMathlib`, `HexPolyMathlib`,
`HexPolyFpMathlib`, and `HexMvPolyMathlib`, plus Mathlib. These provide
algorithm correctness and coefficient transport without placing Mathlib
imports in `HexDet`. Add `HexModularMatrixMathlib` when the modular arm is
integrated. No dependency points back from those providers to dispatch.

The intended files are `HexDetMathlib/{Basic,Small,Bareiss,Berkowitz,Field,Carriers}.lean`
and the umbrella `HexDetMathlib.lean`. A modular correspondence module is
added with that algorithm. Build-only examples exercise the laws and
instance resolution. They do not duplicate the owner's runtime conformance.

## Contract

The following declarations are proposed obligations, not existing theorems.
Use namespace `HexDetMathlib` for the companion declarations below, with
`open Hex.Det` for the executable API. Define one relation
`ValidRoute (policy : Policy R) (A : Hex.Matrix R n n) (result : Result R)`.
It follows the constructors of `Policy` and the branches of `runWith`:
selection obeys the policy, each route transition is justified by the actual
failure equation of the attempted operation, and the returned value equals
the completed arm's result with the policy's coefficient operations and
parameters on the same input. A small completion additionally asserts
`n ≤ 2`. Endpoint consistency and nonemptiness hold by construction of
`Route`. This definition must not trust the reported tags or hide an
unspecified per-producer predicate.

The proposed law class for an explicit policy is:

```lean
class LawfulPolicy [Lean.Grind.CommRing R] (policy : Policy R) : Prop where
  value_eq : ∀ {n} (A : Hex.Matrix R n n),
    (runWith policy A).value = Hex.Matrix.det A
  route_sound : ∀ {n} (A : Hex.Matrix R n n),
    ValidRoute policy A (runWith policy A)

class LawfulDetOps (R : Type u) [Lean.Grind.CommRing R] [DetOps R] : Prop where
  lawful : LawfulPolicy (DetOps.policy (R := R))

theorem det_eq [Lean.Grind.CommRing R] [DetOps R] [LawfulDetOps R]
    (A : Hex.Matrix R n n) : Hex.Det.det A = Hex.Matrix.det A

theorem det_eq_mathlib [CommRing R] [DetOps R] [LawfulDetOps R]
    (A : Hex.Matrix R n n) :
    Hex.Det.det A = Matrix.det (HexMatrixMathlib.matrixEquiv A)
```

For each policy constructor, prove `LawfulPolicy` by splitting on its actual
dispatch and fallback branches and using the arm theorems below. The
exact-quotient constructor requires the cancellation law for its stored
quotient. Field policies require the carried division's explicit law
`∀ a b : R, b ≠ 0 → div (a * b) b = a` for the initial Bareiss arm, and
field laws over the ambient commutative-ring operations for elimination.
The field constructor's evidence supplies these laws, rather than a second
ring on the same type.

The integer recipe's constructor proof takes mutual inverse laws for
`toInt` and `ofInt` and preservation of `0`, `1`, addition, negation, and
multiplication. Prove the finite Leibniz sum commutes with these maps and
transport the integer arm equality back to `R`. For the shipped `Int`
instance the maps and this transport are identities. When the modular arm
is enabled, the constructor proof additionally takes
`[Hex.Matrix.LawfulDetBound]` from the lower library. Instantiate
`LawfulDetOps` for each shipped default from these constructor proofs.
Explicit test policies, including zero fuel, use `LawfulPolicy` directly.
The theorem for an arbitrary `DetOps` always requires laws for that same
instance's policy. A supplied quotient cannot be declared correct without
its law.

`det_eq` unpacks `LawfulDetOps.lawful` and projects the default policy's
`value_eq`. The `lawful` field is not itself a registered instance.
`det_eq_mathlib` composes it with `HexMatrixMathlib.det_eq`. Although the first law uses only
Mathlib-free types, it lives here and is not available to Mathlib-free
consumers in the first version. In particular, the supplied proofs must not
assume a Mathlib `CommRing` instance exists on every executable carrier.

## Existing proof routes

These are existing declarations, with the paths and hypotheses that the
implementation may actually use:

| Arm or transport | Existing source | Use |
|---|---|---|
| reference to Mathlib | `HexMatrixMathlib.det_eq`, `HexDeterminantMathlib/CoreTransport.lean`, `[CommRing R]` | `Hex.Matrix.det A = Matrix.det (matrixEquiv A)` |
| Bareiss | `HexMatrixMathlib.bareissWith_eq_mathlib_det`, `HexBareissMathlib/Bareiss.lean`, `[CommRing R] [DecidableEq R]`, `quot`, and `∀ a b, b ≠ 0 → quot (a * b) b = a` | compose with the symmetric reference correspondence |
| Bareiss directly to reference | `HexMatrixMathlib.bareissWith_eq_det`, same file and hypotheses | already packages that composition |
| Berkowitz | `HexCharPolyMathlib.coeff_zero_charPoly`, `HexCharPolyMathlib/Coeff.lean`, `[CommRing R] [DecidableEq R]` | `(charPoly A).coeff 0 = (-1)^n * Hex.Matrix.det A` |
| tiny characteristic polynomials | `Hex.Matrix.charPoly_empty`, `charPoly_one_by_one`, `charPoly_two_by_two`, `HexCharPoly/Small.lean`, `[Lean.Grind.CommRing R] [DecidableEq R]` | closed forms for the signed constant coefficient |
| tiny determinants | `Hex.Matrix.det_principalSubmatrix_zero`, `det_one_by_one`, `det_two_by_two`, `HexDeterminant/Leibniz.lean` | reference equalities (the empty case is stated for a zero-sized principal submatrix), under `Lean.Grind.Ring` for sizes zero and one and `Lean.Grind.CommRing` for size two |
| elimination steps | `Hex.Matrix.det_rowSwap`, `det_rowScale`, `det_rowAdd`, `HexDeterminant/RowOps.lean`, `[Lean.Grind.CommRing R]` | determinant effects of the actual row operations |

For Berkowitz, multiply the coefficient theorem by `(-1)^n` and simplify
`(-1)^n * (-1)^n = 1`. This yields the required determinant without a
nontriviality, invertibility, or characteristic restriction. Both signs
matter, particularly in odd dimensions. For the small arm, specialize the
reference equalities or use the small characteristic-polynomial forms
and this same coefficient argument. Neither route runs a full Berkowitz
computation at runtime.

The Bareiss equation is available through the companion, not as a
Mathlib-free theorem merely because its conclusion mentions two executable
definitions. No full Mathlib-free proof of the Berkowitz determinant
identity is claimed. Such a proof is future work and must establish the
same identity over `Lean.Grind.CommRing`, including rings with zero divisors.

## Outstanding arm and carrier obligations

**Field elimination.** There is no existing determinant result obtained by
multiplying the diagonal of `rowReduce`. Prove correctness for the proposed
forward-elimination operation with its accumulated pivot product and swap
sign. The invariant relates that product, sign, and trailing determinant
to the input determinant. Use the row-operation lemmas above. Prove the
failed-pivot column branch yields determinant zero. Until the operation
and its correctness are supplied, the installed field policy is Bareiss.

**Modular and divisor arms.** The operations and correctness in
[hex-modular-matrix](../../SPEC/Libraries/hex-modular-matrix.md) are planned, not declarations
that can be imported today. Once implemented, compose their determinant
equalities with the dispatch branches and discharge `LawfulDetBound` using
the modular companion. The divisor route must also satisfy that library's
certified solve and divisibility contracts. Modular exhaustion must use the
Bareiss proof and report Bareiss completion. Never assume finite fuel always
succeeds or replace the bound by a stabilization test.

**Executable coefficient structures.** `Rat` and the supported `MvPoly`
carriers already have the Mathlib structures needed for generic arm
correspondence. Executable `DensePoly`/`ZPoly` and `ZMod64` do not currently
have global Mathlib `CommRing` instances, as the
[hex-bareiss companion](../../HexBareissMathlib/SPEC/hex-bareiss-mathlib.md#headline-correspondence-theorems)
explains. The existence of the generic Bareiss theorem does not close
those carrier obligations.

The implementation must supply compatible Mathlib algebraic structures in
`HexPolyMathlib` for `DensePoly`/`ZPoly` and `HexPolyFpMathlib` for `ZMod64`,
transported from the mathematical polynomial or residue types while retaining
the executable operations. The private dense-polynomial structure in
`HexResultantMathlib/Specialize.lean` is not a reusable dependency and uses
`npowRec`. Follow the executable-power choices in
`HexMvPolyMathlib/Equiv.lean` and `HexGFqMathlib/Basic.lean`: install the
executable `npow`, rather than introduce a second power operation.
Then the generic arm proofs apply with the same quotient law. Transport
must preserve the exact `Zero`, `One`, `Add`, `Neg`, `Mul`, and `Pow`
operations used by `Lean.Grind.CommRing`, rather than introducing a second
unrelated ring on the type. It must leave computational division and
decidable equality intact. `HexDetMathlib/Carriers.lean` assembles those
instances and the dispatch laws above both dependency chains.

For a custom commutative carrier with only `Lean.Grind.CommRing`, the same
compatibility work or a direct proof of its dispatch law is required in the
companion. The generic class does not manufacture Mathlib structures.
These are implementation prerequisites for the advertised per-carrier
correctness: computation and conformance alone do not complete them. Do
not claim the first version's full correctness until all shipped carrier
instances have laws. No new axiom or silent weakening of the carrier table
is an acceptable substitute.

## Verification

Build-only examples must resolve both `DetOps` and its law for every carrier
listed in the computational SPEC, using `Rat` and prime `ZMod64` for dense
polynomials and `Int` and `Rat` for multivariate polynomials. Include an
explicit custom quotient constructor, the generic Berkowitz default over
a ring with zero divisors, and the trivial ring.

Exercise `det_eq` and `det_eq_mathlib` at empty, one-by-one, two-by-two,
row-swapped, and singular inputs. For integration, call `runWith` to force
each enabled non-small arm at `n > 2` and each available fallback transition, then
apply its
`LawfulPolicy.route_sound` law. Tiny-size cross-arm comparisons call the
lower algorithms directly because dispatch always uses the small arm.
Tiny closed values
may be checked with kernel `decide`. Certificate replay and tactic
performance belong to the downstream matrix-tactic libraries. This
companion introduces neither a certificate format nor a trusted evaluator.
