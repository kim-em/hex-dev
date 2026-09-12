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
no row reduction, GCD/LCM search or field division. For rationals use
numerator/positive-denominator data and division-free cross multiplication
for equality; check every denominator is nonzero. The reduction path uses
only list data and exposed structural recursion on `Nat`/`Int`, as in
`HexRank/Kernel.lean`; neither `DensePoly` nor `Hex.Matrix`, `Array`,
`Vector`, `Fin`, `Finset` or well-founded recursion is reduced there.

Required new companion theorem `minpoly_eq_of_checkList` takes dimensions,
input lists, a witness and `checkMinPolyList ... = true`, and concludes
`minpoly F (ofLists n n decodedRows) = decodedPolynomial`. Prove list checks
imply the reference check (decoding stays in the proof, outside reduction),
then use `MinPolyCert.check_sound`, `vectorEquiv_evalVec` and
`minpoly.unique`, just as `equiv_minPoly` uses monicity, annihilation and
minimal degree. Add a wrapper with `hA : A = ofLists ...` and the checked
identification of `p`; both goal orientations reuse this soundness theorem.
No hypothesis asserts that the witness came from the producer.

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
