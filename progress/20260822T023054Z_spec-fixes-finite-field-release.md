# SPEC and record staleness fixes ahead of the finite-field release batch

## Accomplished

Cleared eight release-readiness staleness items across SPECs, `PLAN/`, and
`libraries.yml`. Each claim was checked against the source before editing.

- `HexGF2/SPEC/hex-gf2.md`: the header named hex-poly as the dependency.
  Every import under `HexGF2/` is `HexBasic` or `Std`, so the header now
  names hex-basic. The same paragraph called the packed-versus-generic
  `GF2Poly` / `FpPoly 2` comparisons "planned"; they are registered in
  `bench/HexGF2Bench.lean` under the `packed-vs-generic-comparison` input
  family, so the paragraph now says they exist and locates them by layout:
  cross-library, therefore at the executable root rather than in the
  per-library `bench/HexGF2/` tree.
- `libraries.yml`: `HexGF2.deps` dropped `HexPoly`. No file under
  `HexGF2/`, `bench/HexGF2/`, or `conformance/HexGF2/` imports a `HexPoly`
  module. `bench/HexGF2Bench.lean` imports `HexPolyFp`, which is the
  executable-root cross-library comparison and not a `HexGF2` dependency.
  `scripts/check_dag.py` and `scripts/status.py` agree: the status output
  is byte-identical before and after.
- Comparator-absence tags: `HexPolyFpMathlib`, `HexGF2Mathlib`, and
  `HexGFqMathlib` all cited `proof-only-layer`, which is not one of the
  reasons `SPEC/benchmarking.md` §"Comparator naming" enumerates. All three
  now cite `correspondence-only-layer`, the sixth reason a parallel policy PR
  is adding for a zero-bench correspondence layer, and each names its
  computational performance owners: hex-poly-fp; hex-gf2 and hex-gfq-field;
  hex-gfq-field and hex-gf2. `mathlib-bridge` was the first candidate and is
  wrong here, since `SPEC/benchmarking.md` defines it through a within-Lean
  `compare` group and none of these three has one. This PR must therefore
  land after the policy PR, so the tag is defined before anything references
  it.
- `SPEC/Libraries/README.md`: the hex-poly-fp-mathlib index line advertised
  degree transport. `HexPolyFpMathlib/Basic.lean` has coefficient, monicity,
  derivative, divisibility, and ring-operation transport, but no
  `degree`/`natDegree` lemma, so "degree" is gone from the line.
- `HexGFqMathlib/SPEC/hex-gfq-mathlib.md`: the SPEC covered only
  `Basic.lean` and `GF2q.lean`. Added Contents entries and two sections for
  `Subfield.lean` (the ring homomorphisms out of `FpPoly p`, and
  `conwayEmbed`, the degree-`m` into degree-`n` Conway embedding) and
  `Primitivity.lean` (the component lemmas that would transport hex-conway's
  executable order check onto the hypotheses of Mathlib's
  `orderOf_eq_of_pow_and_pow_div_prime`). Both sections record what is
  *not* proved, since a first draft of them overstated the Lean content on
  two counts. `Conway.normX` is a computed Frobenius-product representative;
  identifying it with the field norm `α ^ ((p^n - 1) / (p^m - 1))` is design
  rationale, and `HexConway/Compatibility.lean` names the two missing
  Frobenius and evaluation bridges explicitly. What is proved is that
  `C(p, m)` vanishes at its class, which is what `conwayEmbed` consumes, and
  `conwayEmbed`'s hypothesis is a `Conway.Compatible` witness on a committed
  divisor pair, not an `m ∣ n` proof. In `Primitivity.lean`, no declaration
  consumes a `Conway.Primitive` witness or produces the per-prime hypothesis
  function Mathlib's order lemma quantifies over, so both the glue from
  `Primitive.check` and the per-entry `orderOf` conclusion are recorded as
  absent.
- `PLAN/Releases.md`: the prime-splitting tutorial was anchored to hex-gfq,
  contradicting the anchor table at `PLAN/Phase7.md:137`. Since the
  authoritative anchor is hex-berlekamp-zassenhaus, a Release 3 library, the
  tutorial bullet moved from Release 2 to Release 3 rather than just
  swapping the anchor name in place: the readiness predicate treats a
  release's tutorials as subsumed by its own libraries' Phase 7.
- `libraries.yml`: the `HexPolyFpMathlib` extraction comment named only
  `HexBerlekampMathlib` as an affected dependent. `HexGF2Mathlib` gained the
  same edge in the same PR (its `equivPolynomial` composes with
  `HexPolyFpMathlib.fpPolyEquiv`) while sitting at `done_through` 4, so the
  comment now covers it too.

## Current frontier

Branch `spec-fixes-finite-field-release`, committed locally, not pushed.
`check_released_manifest.py`, `check_dag.py`, and `status.py` all pass, and
`status.py`'s output is unchanged by the dependency edit.

## Next step

Open the PR, and sequence it after the policy PR that defines
`correspondence-only-layer`, so the tag these three SPECs cite is never a
dangling reference. No mechanical check enforces comparator-absence tags
today, so nothing goes red either way; the ordering is about the text being
true when it lands.

Two adjacent staleness items were found and deliberately left alone, since
they belong to the planned-graph layer of
`SPEC/Libraries/README.md` rather than to the release batch:

- line 146 lists hex-gf2's dependencies as "hex-poly, hex-basic,
  hex-finite-field", but that section describes the planned graph including
  libraries that do not exist yet (hex-finite-field among them), so it is
  not simply a stale copy of `libraries.yml`.
- line 190 lists hex-gfq-mathlib's dependencies as hex-gfq alone, while
  `libraries.yml` has `[HexGFq, HexGF2Mathlib]` and the SPEC header names
  hex-gf2-mathlib.

Both want a decision about whether that section tracks `libraries.yml` or
the planned graph, which is a larger question than this batch.

## Blockers

None.
