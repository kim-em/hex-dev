# HexPolyFp Phase 6 API Review

## Scope

Audited:

- `SPEC/Libraries/hex-poly-fp.md`
- `PLAN/Phase6.md`
- `HexPolyFp/Basic.lean`
- `HexPolyFp/PrimeField.lean`
- `HexPolyFp/Frobenius.lean`
- `HexPolyFp/ModCompose.lean`
- `HexPolyFp/Quotient.lean`
- `HexPolyFp/QuotientFrobenius.lean`
- `HexPolyFp/SquareFree.lean`
- `reports/hex-poly-fp-performance.md`

The review focused on Phase 6 API quality: theorem shape, public/private
boundaries, characterising lemmas, automation annotations, and whether the
surface matches the SPEC without forcing downstream users to unfold executable
implementation details.

## Findings

### 1. Square-free correctness theorems expose internal invariant providers

Priority: high.

`squareFreeDecomposition` is the public executable API in
`HexPolyFp/SquareFree.lean`, but two of the main correctness theorems still
require callers to supply proof-internal invariants:

- `squareFree_pairwise_coprime` takes a `stateProvider` over
  `yunFactorsDerivativeActiveReachable`.
- `squareFree_weightedProduct` takes both a `residualInvariant` over
  `squareFreeAuxRevResidualSatisfied` and a `hstate` provider over
  `yunFactorsDerivativeActiveReachable`.

That is not a Mathlib-quality public theorem shape for the decomposition. The
callers should see closed facts about the actual output of
`squareFreeDecomposition`, not the reachability machinery used to prove them.
The current public API also lacks a direct exported theorem that every emitted
factor has positive multiplicity, even though the module docstring describes
positive-multiplicity factors and the SPEC calls out square-free decomposition
characterising lemmas.

Worker-sized follow-up:

- Prove the provider obligations privately from the existing reachable-state
  lemmas.
- Add closed public wrappers, for example:
  - `squareFreeDecomposition_weightedProduct`
  - `squareFreeDecomposition_pairwise_coprime`
  - `squareFreeDecomposition_multiplicity_pos`
- Keep the current provider-parametric lemmas private or move them under an
  internal namespace if they remain useful as proof plumbing.

Relevant declarations:

- `SquareFreeFactor`, `SquareFreeDecomposition`
- `weightedProduct`
- `squareFreeDecomposition`
- `squareFree_pairwise_coprime`
- `squareFree_weightedProduct`
- `squareFree_factors_squareFree`

### 2. Quotient root-count and finite-field facts blur the HexPolyFp boundary

Priority: high.

`HexPolyFp/Quotient.lean` starts with a compact quotient API, but the public
surface later includes finite-enumeration, root-count, multiplicative-group,
Frobenius fixed-point, and degree-divisibility facts:

- `elements`, `mem_elements`, `elements_nodup`, `elements_card`
- `nonzeroElements`, `nonzeroElements_card`
- `evalCoeffList`, `dividedDifferenceCoeffs`, `rootsOfCoeffList`
- `rootsOfFpPoly`, `eval_rootsIn_elements_length_le_degree`
- `listProd`, `pow_pred_card_eq_one_of_ne_zero`, `pow_card_eq_self_of_irreducible`
- `deg_dvd_of_pow_pPowN_eq_self_universal`

Some of these are currently consumed by `HexBerlekamp/RabinSoundness.lean`, so
they are real proof infrastructure. The issue is the boundary: they are not
basic specialized polynomial arithmetic over `Z/pZ`; they are finite-field
cardinality and root-count theorems for an irreducible quotient. Keeping all of
them public in `HexPolyFp` makes the layer look broader than the SPEC describes
and preempts the future `HexGFqMathlib`/bridge-layer split.

Worker-sized follow-up:

- Split `Quotient.lean` into a small public quotient-operation surface and an
  explicitly proof-facing internal surface.
- Move root-count/divided-difference/list-product helpers under a
  `Quotient.Internal` namespace or into the Rabin/bridge file that consumes
  them.
- Keep only stable quotient operations and characterising lemmas public:
  `reduce`, `Congr`, arithmetic operations, `eval`, `eval_C`, `eval_X`,
  `eval_add`, `eval_sub`, `eval_C_mul`, `eval_monomial`, and inverse
  cancellation under irreducibility.

### 3. Basic polynomial algebra has conservative simp coverage gaps

Priority: medium.

`HexPolyFp/Basic.lean` proves a substantial semiring-like API directly over
`FpPoly`, but several neutral and cancellation lemmas are untagged while later
proofs repeatedly rewrite them manually:

- untagged: `add_zero`, `zero_add`, `add_left_neg`, `add_right_neg`,
  `sub_zero`, `zero_sub`, `sub_self`, `sub_eq_add_neg`
- tagged: `zero_mul`, `mul_zero`, `one_mul`, `mul_one`

This is not a correctness bug, but it leaves downstream proofs noisier than
necessary and is out of step with the Phase 6 goal of conservative automation
for normalization lemmas.

Worker-sized follow-up:

- Audit the basic algebra theorem set and add `@[simp]` only to normalization
  lemmas whose rewrite direction is unambiguous.
- Include smoke tests analogous to the existing coefficient-level simp smoke
  tests near the top of `Basic.lean`, so future edits do not regress the
  intended automation surface.

### 4. Public schoolbook coefficient helpers need an explicit proof-facing home

Priority: medium.

`FpPoly.mulCoeffTerm` and `FpPoly.mulCoeffSum` are public and used outside
`HexPolyFp`, especially by Hensel lift proofs. They are legitimate
proof-facing infrastructure, but their current placement beside ordinary
polynomial constructors makes them look like part of the computational API.
They also duplicate the generic `DensePoly.mulCoeffSum` vocabulary, increasing
the chance that downstream code unfolds the wrong layer.

Worker-sized follow-up:

- Keep the helpers available for Hensel proofs, but move them into a clearly
  named proof-facing namespace such as `FpPoly.Internal` or document the
  contract in a local section header.
- Preserve the public theorem `coeff_mul` as the intended characterising lemma
  for users who only need coefficients of multiplication.
- Update the two Hensel imports that unfold these helpers if the namespace is
  changed.

## Audited Surfaces With No Follow-Up Needed

- `HexPolyFp/PrimeField.lean`: the field instance is narrow and appropriately
  tied to `ZMod64.PrimeModulus`; the public lemmas are small and directly
  useful for the instance.
- `HexPolyFp/Frobenius.lean`: the production square-and-multiply path is
  characterised by remainder lemmas and by equivalence to the kernel-reducible
  linear path. The `frobeniusXPowMod_succ` and monomial-mod lemmas are the
  right downstream shape for Rabin-style arguments.
- `HexPolyFp/ModCompose.lean`: the modular-composition API has the expected
  executable definition plus both `modByMonic` and `%` characterisations.
  The simp lemmas only normalize already-reduced results and do not appear
  overly aggressive.
- Performance evidence in `reports/hex-poly-fp-performance.md` is aligned with
  the SPEC requirements: `powModMonic` and square-free reconstruction use
  square-and-multiply style helpers, and factor accumulation avoids repeated
  append in the executable path.

## Verification Notes

The report is review-only and does not implement the follow-up fixes. The
recommended follow-ups are deliberately worker-sized so planners can split them
without rereading the full library.
