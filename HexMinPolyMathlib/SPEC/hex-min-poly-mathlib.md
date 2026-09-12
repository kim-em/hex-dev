# hex-min-poly-mathlib

`hex-min-poly-mathlib` is the proof-only correspondence layer between the
Mathlib-free executable API in `hex-min-poly` and Mathlib's matrix and
polynomial theory. It adds no competing computational implementation.

## Correspondence

For a field `F` with decidable equality, `equiv_minPoly` proves

```lean
equiv (Hex.Matrix.minPoly A) = minpoly F (matrixEquiv A).
```

`vectorEquiv_evalVec` identifies executable Horner evaluation on a vector
with Mathlib `aeval` followed by `mulVec`. Consequently,
`vecMinPoly_dvd_iff` says that the converted vector order divides a Mathlib
polynomial exactly when that polynomial annihilates the converted vector.
`equiv_lcm` identifies `Hex.DensePoly.lcm` with Mathlib's normalized LCM.

## Consequences

The bridge proves that the executable minimal polynomial:

- divides the executable characteristic polynomial;
- has degree at most the matrix dimension;
- is invariant under transposition;
- is invariant under conjugation by a unit, hence under similarity.

The characteristic-polynomial consequences depend on
`hex-char-poly-mathlib`. The executable algorithm and reference certificates belong to `hex-min-poly`.
The tactic specified below adds a proof-performance surface to this companion.

## Performance classification

The existing correspondence is a proof-only Mathlib layer; its computational
performance owner is `hex-min-poly`. Implementing the tactic below requires
companion conformance and a `proof_probes` reservation, with fresh-module
evidence rather than a Mathlib-importing benchmark executable.

## Frontend implementation and validation

The tactic contracts below are design requirements. Their kernel-certificate
subsections specify additions owned by the Mathlib-free algorithm library;
they do not move that code into this companion. When implementing those
additions, cross-link the algorithm's kernel-certificate SPEC to this contract.
Keep existing phase evidence as evidence for the existing correspondence only.
Before activating the frontend, remove `correspondence_only: true` if present,
add `proof_probes: [bench/HexMinPolyMathlib/ProofProbe]`, and reopen the
library's conformance/performance obligations: cap `done_through` at `2` until
the new build-only proof tests pass, then at `3` until complete proof evidence
passes. Do not add an empty reservation while retaining a completed Phase 4.
This SPEC-only change does not alter the manifest or attest implementation.

Proof tests live in `HexMinPolyMathlib/Tests.lean`, built with the ordinary
library; malformed list certificates also belong in the algorithm library's
Mathlib-free conformance driver. Proof probes are fresh modules, not runtime
oracle drivers or Mathlib-importing benchmark executables. Each frontend uses
`HexMinPolyMathlib/Tactic.lean`; result records and list soundness belong
in `HexMinPolyMathlib/Kernel.lean`. No library name changes.

For the named families below, shipping requires complete clean-tree evidence
under the `absolute_only` mode of
[SPEC/benchmarking.md](../../SPEC/benchmarking.md#fresh-module-proof-evidence).
Preregister six rounds and a per-candidate absolute build budget of 60 seconds
on the measurement host for every stated rung. Every candidate sample must
meet it; report the median and kernel-only time as well. A timeout, incomplete
pair, budget failure or provenance mismatch blocks the frontend's performance
sign-off. This is an operational shipping gate, not an asymptotic or portable
wall-time claim. Retain slow completed samples; do not trim the ladder to get
a passing verdict. Any budget revision requires an explicit SPEC amendment.

## The `min_poly` tactic

This section specifies an extension, not an implemented frontend. Follow
[the matrix tactic protocol](../../SPEC/matrix-tactics.md) and
[hex-rank-mathlib §The `rank` tactic](../../HexRankMathlib/SPEC/hex-rank-mathlib.md#the-rank-tactic).
New witness/checker/producer declarations belong to `HexMinPoly`; their
Mathlib soundness and frontend belong here. No additional library is needed.

### Goals, result and carriers

Declare `min_poly` once as a non-reserved tactic atom; `min_poly% A` is the
term form. For closed square `A : Matrix (Fin n) (Fin n) F`, accept
`minpoly F A = p` and `p = minpoly F A`, with a closed polynomial `p`.
The term form returns the existing shared
`Certified (fun A => minpoly F A) A`, whose `value : Polynomial F` and
`proof : minpoly F A = value` expose the computed result. The empty matrix
has minimal polynomial `1`, including the zero-dimensional algebra case.

Soundness takes Mathlib `[Field F] [DecidableEq F]`, with the induced
`Field.toGrindField` selected before executable inputs and certificates
are formed. The initial numeric frontend must support `ℚ`, including
nonintegral coefficients. A field instance alone does not supply a literal
codec: arbitrary abstract fields, symbolic entries and unsupported closed
field expressions are outside this handler. Prime `ZMod p` is an extension
once a proved residue codec is available; composite moduli are not fields.

Use the [shared literal layer](../../HexMatrixMathlib/SPEC/hex-matrix-mathlib.md#matrix-literals)
for matrix recognition and identification. Request against that SPEC:
field-aware argument elaboration and rational/residue entry codecs with
proved decoding and arithmetic agreement. Against
[hex-poly-mathlib](../../HexPolyMathlib/SPEC/hex-poly-mathlib.md), request a
closed Mathlib polynomial literal adapter to ascending coefficient lists,
with a proof identifying the target polynomial. These are adapter requests,
not local competing reifiers. The polynomial checker belongs to HexMinPoly.

### Kernel certificate and soundness

Existing `Hex.Matrix.MinPolyCert` in `HexMinPoly/Cert.lean` carries `poly`,
one `OrderCert` per standard basis vector, and one `LcmStep` per LCM fold.
`MinPolyCert.check_sound`, under `[Lean.Grind.Field F] [DecidableEq F]`,
proves monicity, annihilation on every vector, and divisibility into every
annihilator. It does **not** directly state equality with Mathlib `minpoly`.
`HexMinPolyMathlib.equiv_minPoly` in `Basic.lean` identifies the executable
`minPoly` under Mathlib field assumptions, but reducing that producer is
not the tactic proof path.

Require a new `MinPolyWitness` and `checkMinPolyList` that reshape precisely
this certificate: ascending coefficient lists for all polynomials, a list
of `n` orders `(poly, deg, inv)`, and a list of `n` LCM steps. Matrices,
including each `n × deg` right inverse, are row lists. Validate exact lengths,
`deg ≤ n`, polynomial normalization (no trailing zero except the empty zero
polynomial), monicity and every dimension before arithmetic. In basis-index
order check:

- the order polynomial has degree `deg`, is monic and annihilates its
  standard basis vector;
- the `deg × n` Krylov row matrix times `inv` is the identity, certifying
  independence of all lower powers, not just annihilation;
- starting at `running = 1`, each step satisfies the existing four identities
  `running = common * left`, `incoming = common * right`,
  `bezoutLeft * running + bezoutRight * incoming = common`, and
  `result = left * incoming`; the final result equals `poly` and is monic.

Krylov powers and Horner evaluation are structural list recursions, with
no row reduction, GCD/LCM search or field division. For rationals follow the
scaled-integer boundary of `checkDetRat` in
`HexBareiss/Kernel.lean`: retain the input row list at `Rat` for cheap literal
identification, and check its agreement with integer rows `Z` and a single
positive scale `D`, so `A = Z / D`, by numerator/denominator cross products.
This scaling is for certificate arithmetic; it does not claim that scaling
preserves the minimal polynomial. Give each polynomial and inverse block its
own positive common denominator, check those scale factors, and multiply out
all denominator powers in the identities. The shared codec supplies the
literal/encoding agreement proof; `A = ofLists ... rationalRows` remains
`rfl` for numeral literals, never `A = ofLists ... (decode encodedRows)`.

Recompute Krylov powers as integer vectors `Z^k eᵢ` with known scale `D^k`.
The annihilation check for a degree-`d` polynomial with common denominator `s`
checks the numerator of `s * D^d * p(A)eᵢ` using those powers. Do not multiply
unreduced per-entry denominators at each dot-product addition. If `b` bounds
bit heights in `Z` and `D`, power entries and scales have
`O(k * (b + log(n + 1)))` bits; record this scaled input height separately
from the original entry heights. Supplied polynomial/inverse numerators add
their own recorded bit heights. LCM identities use integer coefficient
convolutions with common denominators cleared once per identity.
The reduction path uses
only list data and exposed structural recursion on `Nat`/`Int`, as in
`HexRank/Kernel.lean`; neither `DensePoly` nor `Hex.Matrix`, `Array`,
`Vector`, `Fin`, `Finset` or well-founded recursion is reduced there.

Required new companion theorem `minpoly_eq_of_checkList` takes dimensions,
input lists, a witness and `checkMinPolyList ... = true`, and concludes
`minpoly ℚ (ofLists n n rationalRows) = decodedPolynomial` on the initial
rational arm (with the corresponding transport for any later field codec).
Prove list checks
imply the reference check (decoding stays in the proof, outside reduction),
then use `MinPolyCert.check_sound`, `vectorEquiv_evalVec` and
`minpoly.unique`, just as `equiv_minPoly` uses monicity, annihilation and
minimal degree. Add a wrapper with `hA : A = ofLists ...` and the checked
identification of `p`; both goal orientations reuse this soundness theorem.
No hypothesis asserts that the witness came from the producer.

The basis-wide certificate stores `O(n³)` inverse scalars in the worst case
(`deg ≤ n` for each of `n` orders), plus the LCM/Bézout polynomial coefficients,
whose supplied lengths and heights must also be recorded. Krylov reconstruction
and inverse checks cost `O(n⁴)` scalar operations overall; polynomial identity
checks additionally cost the pairwise products of their coefficient lengths.
These are arithmetic counts, not a bit-complexity claim. The advertised first
release is bounded to dimension `16`; larger inputs are `declined` with the
configured dimension budget. The bound is a frontend capability limit, never
a hypothesis of `minpoly_eq_of_checkList`. Retain the existing basis-wide
certificate to reuse its proved minimality contract; any smaller certificate
requires a separate soundness argument and new measured evidence.

Required initial rational API schemata, with the integer-encoded witness
fields specified above and a proved coefficient decoder `decodePoly`:

```lean
-- HexMinPoly/Kernel.lean, namespace Hex.Matrix
def checkMinPolyList (n : Nat) (rows : List (List Rat))
    (c : MinPolyWitness) : Bool

-- HexMinPolyMathlib/Kernel.lean, namespace HexMinPolyMathlib
theorem minpoly_eq_of_checkList {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℚ) (rows : List (List Rat))
    (c : Hex.Matrix.MinPolyWitness)
    (hA : A = HexMatrixMathlib.ofLists n n rows)
    (hc : Hex.Matrix.checkMinPolyList n rows c = true) :
    minpoly ℚ A = decodePoly c

-- Type returned by min_poly% A:
abbrev MinPolyResult {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ) :=
  HexMatrixMathlib.Certified (fun M => minpoly ℚ M) A
```

The exposed kernel checks read rational input numerators/denominators once
for scale agreement, as `checkDetRat` does; Krylov and polynomial arithmetic
then use only the encoded integer lists. `decodePoly` is used in the theorem
statement and transport proof, not as a polynomial computation in the check.
General field transport is parametric in a proved codec, as required above.

### Producer and proof assembly

Run compiled `Hex.Matrix.minPolyCert` from `Producer.lean`, convert its
output to the list witness, and re-check it with the compiled list checker
before quotation. This preserves the roles of `rankWitness`, the literal
identification, and `rank_eq_of_checkList'` in the rank implementation.
Build the Boolean proof by kernel reduction and emit the complete goal proof
as one synchronous `mkAuxTheorem`, with no elaborator kernel pre-check.
`!![…]` uses definitional identification; other supported literal routes
use the shared adapter's single identification proof.

Follow `notApplicable`/`declined`/`success`/`failure` from the shared protocol.
A different operation or unsupported field fragment is `notApplicable`;
a missing codec or exceeded budget within the advertised fragment is
`declined`, naming the capability or entry. A false target reports the
computed polynomial; a malformed producer certificate or kernel rejection
is `failure`. Diagnose only after rejection, without replaying `minPoly`.

### Conformance and proof probes

Add companion proof tests for both orientations and the term record, each
literal route, bounded unfolding, false polynomials and unsupported carriers.
Refute malformed witnesses: omitted/reordered basis orders, wrong list
lengths, excessive degree, corrupted right inverse, an annihilator of larger
than minimal degree, a broken Bézout identity, wrong final polynomial,
nonmonic output and zero denominators. Use mutations known to violate the
identity (not changes to unused data). Audit accepted theorem axioms: only
`propext`, `Classical.choice`, `Quot.sound`, never `sorryAx` or native trust.

Reserve `bench/HexMinPolyMathlib/ProofProbe` in `libraries.yml` when the
frontend is implemented. Named seeded families are `cyclic` (companion
matrices), `repeated-block` (identical blocks, minimal degree below dimension),
`nilpotent` (Jordan blocks), and `rational-dense`; dimensions `2, 4, 8, 16`
and input heights `8, 32` bits, plus `0 × 0` as a correctness probe.
Mathlib has no corresponding tactic, so no comparator ratio or superiority
claim is required. Per [fresh-module evidence](../../SPEC/benchmarking.md#fresh-module-proof-evidence),
record six complete samples paired with import-only baselines, adjacent and
alternating orientation, raw absolute build times and their median, baseline
deltas, one kernel-only profile per family, certificate entry counts and
serialized bytes, largest numerator/denominator bit lengths, emitted artifact
sizes and axiom sets. Retain provenance, all completed samples and timeouts;
preregister operational caps without treating them as portable performance
claims. Executable producer/checker benchmarks remain in HexMinPoly.
