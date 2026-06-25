# Conformance testing

Conformance testing cross-checks Lean implementations against either
(a) independently stated algebraic properties, or (b) an external
oracle (`python-flint`, `fpylll`, `cypari2`, or the committed Frank
Lübeck Conway cache). The goal is to catch implementation bugs
*before* proof work starts. No point proving theorems about wrong
implementations.

When conformance fails, the response is the same as when benchmarking
returns an unexpected complexity verdict ([benchmarking.md](benchmarking.md)):
file a GitHub issue ([PLAN/Conventions.md §Bench-found and
conformance-found issues](../PLAN/Conventions.md#bench-found-and-conformance-found-issues))
and roll the affected library's `done_through` backward
([PLAN/Conventions.md §Rollback is a normal action](../PLAN/Conventions.md#rollback-is-a-normal-action)).
Conformance and benchmarking share one bug-finding loop; the choice
of harness depends on which axis the bug is on (output correctness
vs. algorithmic complexity), but the response is uniform.

Conformance testing is a tiered system rather than one monolithic
workflow. The repository supports three profiles:

- `core` — deterministic Lean-only checks with no external dependencies.
  Runs on every push and every pull request. MUST be green to merge.
- `ci` — modest randomized cross-checks against external oracles, run
  only when the oracle is available on the runner. Runs on every push
  and every pull request; oracle-missing cases are recorded as skipped.
- `local` — developer-driven runs with customisable sizes and tools.
  Triggered via `workflow_dispatch` or run by hand; not a merge gate.

Every failure must be replayable: record the library, profile, seed,
fully serialised input, and the oracle (if any) in the failure report.

## Per-library module contract

Every library `HexFoo` at `done_through ≥ 2` MUST provide
`HexFoo/Conformance.lean`, re-exported from `HexFoo.lean`. This module
is the `core` profile for `HexFoo`. It MUST:

1. **Open with a docstring** declaring the library-specific
   conformance contract:

   - **Oracle:** which external oracle applies, or `none`.
   - **Mode:** `always` / `if_available` / `required`.
   - **Covered operations:** bulleted list of the public operations
     this module exercises (matches the library's SPEC API surface).
   - **Covered properties:** bulleted list of the algebraic /
     structural properties this module asserts via `#guard`
     (Bézout, degree bound, round-trip identities, etc.).
   - **Covered edge cases:** bulleted list of the edge inputs
     exercised (zero / empty / identity / modulus-1 / singular /
     degree-0, as applicable).

   This docstring is the library's local conformance spec, written
   by the agent doing the Phase 3 work. Reviewers check the rest of
   the file against this docstring.

2. **Cover every advertised operation** listed in the library's
   SPEC API surface with at least one elaboration-time check
   (`#guard`, `#guard_msgs in #eval`, or `example ... := by decide`)
   that evaluates the operation on a concrete committed input and
   asserts the result.

3. **Check every advertised algebraic property** on committed
   inputs — not just spot values. Worked examples:

   - `extGcd a b = (g, s, t)` → `s * a + t * b = g` and
     `g = Nat.gcd a.natAbs b.natAbs`.
   - `det`, `rowSwap` → `det (rowSwap M i j) = -det M` for `i ≠ j`.
   - `rowScale` → `det (rowScale M i c) = c * det M`.
   - `rowAdd` → `det (rowAdd M i j c) = det M` for `i ≠ j`.
   - Polynomial multiplication → `(p * q).degree ≤ p.degree + q.degree`
     on committed pairs; commutativity on the same pairs.
   - Factorisation → product of committed factors equals the committed
     input; each factor certified irreducible by the library's own
     irreducibility checker (not `native_decide`).

4. **Provide ≥3 cases per advertised operation**, covering:
   - one *typical* input (non-edge, non-degenerate);
   - one *edge* input (zero / empty / identity / modulus-1 / singular
     / degree-0, as applicable);
   - one *adversarial* input (hand-crafted to exercise a known failure
     mode — e.g. trailing zero coefficients for polynomial
     normalisation, a swap of non-adjacent rows for determinant sign,
     a modulus equal to a power of two for modular reduction).

5. **Store each case's inputs and expected outputs in exactly one
   place** in the source — inline in the `#guard` / `example` /
   `#guard_msgs` line, or via a single `let`-bound value referenced
   by the check. No parallel "expected" struct fields that the check
   doesn't reference.

6. **Use `#guard_msgs in #eval` for spot values** whenever the
   expected output is small enough to read in-source. This form makes
   the expected value visible to reviewers and fails at elaboration
   (hence in CI) if the evaluator changes:

   ```lean
   /-- info: (6, 1, -2) -/
   #guard_msgs in #eval HexArith.extGcd 30 12
   ```

7. **Use `#guard` for property assertions** — they turn any
   Bool-valued invariant into a CI-enforced check:

   ```lean
   #guard let (g, s, t) := HexArith.extGcd 30 12; s * 30 + t * 12 = g
   ```

8. **Exercise top-level entry points end-to-end.** When the library
   SPEC names a public top-level entry point (e.g.
   `HexBerlekampZassenhaus.factor`), at least one conformance case
   per such entry point must call it with a raw input and assert the
   output — not bypass it via internal-stage helpers (e.g. supplying
   pre-lifted factors directly to `recombine`). Internal-stage checks
   are useful but not a substitute: they cannot detect a
   wrong-asymptotic intermediate stage that the entry point would
   exercise at realistic input sizes.

## Oracle discipline

Every operation in a library's SPEC API surface that is exercised by
fixtures via `HexFoo/EmitFixtures.lean` MUST have an external-oracle
cross-check that satisfies all three rules below. A SPEC declaration
that names an operation but cannot be paired with an oracle satisfying
these rules is not Phase-3-ready: file the oracle issue first and hold
the library at `done_through ≤ 2`.

1. **Independent expected value.** The oracle computes the expected
   value from the original fixture input, using the oracle's own
   implementation, never by re-running the operation under test on
   Lean's output. Canonicalisation between Lean and oracle outputs
   (e.g. monic-normalisation, sorting by a deterministic key,
   extracting an explicit unit field) is permitted; re-applying the
   operation under test as a "canonicalisation" is not. An oracle
   that re-factors each component of Lean's factorisation through
   FLINT and compares the union as a multiset accepts any Lean
   output the oracle's own factor call can refine to the right
   answer — including Lean returning the input unchanged. That is
   not a cross-check.

2. **Uniform contract on every input class.** No input-shape-dependent
   bypass to a strictly weaker invariant. If the fixture set covers
   square-free and non-square-free inputs, both must be cross-checked
   against the same correctness contract. A self-consistency invariant
   like `∏ buckets · residual = f` is a sanity check, not a
   cross-check. If a class genuinely cannot be cross-checked under the
   same contract, remove it from the fixture set or split it into a
   separate operation with its own oracle.

3. **Explicit non-coverage is a tracking obligation.** An emitted
   operation that has no external oracle (whether deferred or
   genuinely blocked) must be paired with an open `directive`
   issue, linked from both `EmitFixtures.lean` and the corresponding
   oracle script's docstring. The library's `Conformance.lean`
   docstring must not claim the operation as covered. Self-consistency
   invariants are not a substitute for an external oracle and must
   not be advertised as conformance coverage.

For factorisation operations specifically, the canonical oracle
pattern is **multiplicity-bucket comparison**: factor the input via
the oracle into its irreducibles `∏ pᵢ^eᵢ`, group by exponent,
monic-normalise each side, and require Lean's output to be a valid
refinement of the oracle's irreducible decomposition under the
operation's documented bucket semantics (full irreducible
factorisation, distinct-degree factorisation, square-free
decomposition, etc.). This pattern is strict (rejects unfactored or
under-decomposed Lean outputs) while still admitting the legitimate
non-uniqueness of factor order.

## Banned anti-patterns

These patterns have produced ceremony-heavy modules with no teeth and
MUST NOT appear in any `Conformance.lean`:

- **Dead "expected" struct fields.** Every field named `expectedX`
  (or otherwise representing an expected output) must appear on the
  RHS of at least one `#guard` / `example` / `by decide` check in
  the same file. If a fixture structure carries expected values the
  `eval` function throws away with `_`, delete the fields.

- **Serialise-and-compare-to-reconstructed-literal.** Checking
  `serialiseMatrix (intMatN a00 a01 …)` against `[[a00, a01, …]]`
  tests that the serialiser is the identity; it does not test the
  operation under study. Assert the *operation's* output directly.

- **Trivial `by decide` where RHS is a copy of the LHS's evaluation.**
  `by decide` on `fixtures.map evalFixture = [literalCopyOfEvaluation]`
  proves only that evaluation is deterministic. The assertion must
  carry content the evaluator alone does not: an algebraic identity,
  an oracle-supplied expected value, or a cross-implementation
  agreement.

- **Metadata `def`s with no consumer.**
  `def library : String := "HexFoo"`, `def profile : String := "core"`,
  `def seed : Nat := 0` are prohibited unless a named driver (CI
  workflow step, Python oracle script) actually reads them.

- **Single-case-per-operation fixtures.** Minimum three cases per
  operation, per §"Per-library module contract" item 3.

- **Duplicated literal data.** Each case's inputs and expected
  outputs appear in source exactly once. No `rawRows : List (List
  Int)` alongside `matrix := intMatN …` alongside a third copy on the
  RHS of `by decide`.

- **Literal duplication across `#guard_msgs` and `#guard`.** A
  `#guard X = [literal]` that immediately follows a `#guard_msgs in
  #eval X` producing the same `[literal]` is redundant — the
  expected value appears twice. Use one idiom per case:
  - `#guard_msgs in #eval X` when the expected value fits on one
    line and belongs in the source for reviewer benefit.
  - `#guard X = formula(inputs)` when there is a closed-form
    identity (`n % p`, `Nat.gcd a b`, `a * b % c`, Bézout, etc.)
    that carries more content than a literal copy.

  `#guard_msgs` documents *what the evaluator produces*; `#guard`
  against a formula documents *what the contract says it should
  produce*. Both together on the same case is either duplication or
  contradiction.

- **Scaffold-locking `#guard`s.** A `#guard` that asserts against
  *current stub output* rather than against the SPEC contract —
  e.g. `#guard (rref M).rank = 0` when `rref` is a placeholder —
  locks the wrong answer in and hides the scaffold. Per
  [design-principles.md §7](design-principles.md) and
  [PLAN/Phase1.md](../PLAN/Phase1.md), no data-level placeholders
  are allowed in committed Lean at all; if a conformance test has to
  lock in trivial output to pass, the underlying implementation is
  a placeholder that should not have been committed in the first
  place. Fix the implementation (or remove the declaration until
  it's implementable), don't paper over it with a test that says
  "this wrong output is expected".

  *Process rule.* Don't compute the expected RHS by running the
  function under test, even with the result hand-copied into the
  source. The expected value must be independently derivable from
  the function's documented contract on the committed input —
  via a closed-form identity, an oracle, a hand calculation, or
  a different implementation. If the implementation isn't ready,
  leave a `-- TODO` comment and stop; don't write the `#guard`
  against output you obtained by running the function.

- **`native_decide`.** Banned project-wide (see
  [SPEC.md](SPEC.md#project-wide-proof-policy)). Restated here because
  conformance checks on large fixtures are a common temptation.

- **Conformance modules not reached by `lake build HexFoo`.** Every
  `Conformance.lean` MUST be imported from the library's root module
  so that `lake build HexFoo` elaborates its `#guard`s.

- **Ceremonial API-still-elaborates `example`s.** An `example` whose
  proof reduces entirely to a `sorry`'d declaration produces no
  regression signal — it elaborates iff the API surface still
  matches, which is already caught by ordinary `lake build` of any
  importing file. Such examples are actively harmful: they cost
  elaboration time, mislead readers into thinking real coverage
  exists where there's none, and propagate as an anti-pattern
  whenever a future agent copies the file's shape. If the underlying
  theorem is `sorry`, delete the example. The example becomes
  meaningful only when the theorem it relies on has a real proof.

- **`Hex*Mathlib/Conformance.lean` files.** The `Hex*Mathlib`
  libraries are proof-only — they have no executable runtime to
  conform to a contract. A `Hex*Mathlib/Conformance.lean` file
  should not exist. Any `#guard` or `#eval` exercising Hex
  executable code belongs in the computational sibling's
  `Hex*/Conformance.lean` (e.g. checks on `Hex.Berlekamp.rabinTest`
  live in `HexBerlekamp/Conformance.lean`, never in
  `HexBerlekampMathlib/Conformance.lean`).

## `#eval` vs `#eval!`

`#eval e` errors when `e` transitively depends on any `sorry`,
including `sorry` in Prop-valued proof fields of structures (see
e.g. `HexPoly.DensePoly.ofArray`, which carries a `sorry`'d
`isNormalized` proof field — this makes every `HexPoly.DensePoly`
value's `#eval` refuse). `#eval!` bypasses the safety check.

Prefer `#eval` when it works. Fall back to `#eval!` **only** when
Lean's strict dependency check forces it — that is, when the
structure being evaluated transitively depends on an unproven
theorem-level `sorry`. In that case, a one-line comment above the
`#eval!` should state which sorry-bearing declaration is blocking
plain `#eval`, so future readers know when the `!` can come off.

```lean
-- #eval requires all of DensePoly's propositional fields to be
-- non-sorry; `isNormalized_normalizeCoeffs` is currently `sorry`.
/-- info: [3, 0, -2] -/
#guard_msgs in #eval! (HexPoly.DensePoly.ofArray #[3, 0, -2, 0, 0]).coeffs.toList
```

Do not cargo-cult `#eval!` just because a neighbouring file uses it.
`HexArith/Conformance.lean` uses plain `#eval` throughout — its
computational dependencies are sorry-free — and other libraries
whose computational graph is similarly clean should follow suit.

## `#guard` vs `#guard decide`

Prefer `#guard <bool-expr>` over `#guard decide (<prop>)`. The
`decide` form is only needed when the assertion is a propositional
equation that does not have a `BEq` / `DecidableEq` instance
available directly — quantified statements, equality on types
without `DecidableEq`, and similar cases. `List` of concrete types,
polynomial coefficient comparisons, matrix-entry equality, option of
such, and nearly every other conformance target have `BEq`
instances; plain `#guard` works and is easier to read.

## Oracle strategy

External tools are used for **testing**, not for algorithms — all
actual computation still runs in Lean. The spec declares *which*
oracle applies to *which* library, but individual per-library SPEC
files decide the oracle for that library in the `## Conformance`
subsection. Default oracle assignments:

- `hex-arith` — Lean's built-in `Nat` / `Int` big integer semantics;
  property checks (Bézout, `Nat.gcd` agreement) sufficient for `core`.
- `hex-mod-arith` — Lean big-integer modular arithmetic as property
  oracle.
- `hex-poly`, `hex-poly-z`, `hex-poly-fp` — `python-flint` primary
  for univariate polynomial arithmetic.
- `hex-matrix`, `hex-gram-schmidt` (released — oracle conformance runs in their own repos) — `python-flint` exact
  (`fmpz_mat` / `fmpq_mat`); numpy/scipy float for well-conditioned
  float-level cross-checks; `fpylll`'s `GSO.Mat` for Gram-Schmidt
  size-reduction parity.
- `hex-gf2`, `hex-gfq-ring`, `hex-gfq-field`, `hex-gfq` —
  `python-flint` (`nmod_poly`, `fq_nmod`, `fq_default`); `cypari2`
  as a secondary independent finite-field oracle when independence
  from FLINT matters.
- `hex-berlekamp`, `hex-berlekamp-zassenhaus` — `python-flint`
  factorisation primary; `cypari2` secondary.
- `hex-hensel` — `cypari2` (PARI `factorpadic`) primary for the
  mod-`p^k` lift surface; `python-flint` does not expose mod-`p^k`
  polynomial factorisation.
- `hex-lll` (released — oracle conformance runs in the hex-lll repo) — `fpylll`, which wraps fpLLL directly, comparing
  reducedness, lattice equality, and determinant preservation rather
  than exact basis equality.
- `hex-conway` — `cypari2` (PARI `ffinit`) plus a committed Frank
  Lübeck flat-file cache for triple-source independence
  (Lean ≡ PARI ≡ Lübeck). No random generation.

The `-mathlib` bridge libraries are not the primary target of
external conformance testing. They rely mainly on internal
equivalence / property tests plus the coverage of the computational
libraries they bridge. Their `core` profile is a set of `#guard`
assertions that the bridge theorems hold on committed small
instances.

## Profile sizes

Size policies per profile. Generators must be parameterised by size
bounds and seed.

- `core`: deterministic cases at the *upper end* of the ranges below
  by default. Shrink only if elaboration time exceeds budget.
  Larger-than-stated inputs are fine if they elaborate fast — these
  are floors of coverage, not ceilings. Polynomial degrees up to
  about `8-12`, matrix dimensions up to about `6-8`, finite-field
  extensions up to degree `6`, LLL dimensions up to about `10`.
- `ci`: modest randomised cases. Integer/finite-field polynomial
  degrees around `16-32`, coefficient bit-sizes around `8-32`, Hensel
  lift exponents around `2-5`, and LLL dimensions around `15-25`
  with small entries.
- `local`: larger campaigns. More seeds, larger degrees/dimensions,
  optional high-cost oracles, manually triggered runs that would be
  too expensive for standard CI.

CI defaults must remain small enough for GitHub-hosted runners and
partial external-tool availability.

## Execution modes

- `always` — no external tools; must run everywhere. The `core`
  profile is always `always`.
- `if_available` — run oracle-backed checks only for tools present on
  the runner; skip (and record the skip) otherwise. The `ci` profile
  is typically `if_available`.
- `required` — manual jobs that fail if declared tools are missing.
  The `local` profile may use `required` when the whole point is the
  oracle being present.

## CI integration

The conformance workflow MUST:

- Run on `push` to `main` and on `pull_request`. Not
  `workflow_dispatch`-only.
- Always run the `core` profile. Any elaboration error in
  `HexFoo/Conformance.lean` fails the job.
- Run the `ci` profile for libraries whose oracle mode is `always`
  or `if_available`. For `if_available`, a missing oracle counts as
  skipped, not failed; the job summary records which oracles were
  skipped.
- For oracle mode `always`, a missing oracle fails the job.
- Keep the `local` profile gated behind `workflow_dispatch`.

Separately, the default `lake build` MUST elaborate every
`HexFoo/Conformance.lean` as part of the ordinary library build, so
even the minimal CI job (no oracle) catches broken `#guard`s.

When the workflow's matrix is derived (e.g. via
`scripts/conformance_targets.py`), ensuring the new library appears
amounts to importing `Hex<X>.Conformance` from `Hex<X>.lean`. When
the matrix is hand-listed, the same PR that lands `Conformance.lean`
MUST update the matrix.

## Infrastructure contract

Lean produces and consumes a simple serialised case/result format —
JSON or JSONL — for:

- polynomials
- matrices
- lattice bases
- primes / modulus choices
- expected normalised outputs

Python or shell driver scripts are responsible for:

- detecting which tools are installed
- invoking external oracles
- normalising oracle outputs into the shared format
- gracefully skipping checks when an optional tool is unavailable

### Layout

The oracle infrastructure is bootstrapped by the `hex-poly`
python-flint cross-check; subsequent libraries replicate the same
pattern.

- **JSONL fixture+result stream.** One record per line. Fixture
  records use kinds `poly` / `matrix` / `lattice` / `prime`; result
  records carry `kind="result"` plus an `op` string and Lean's
  computed `value`. Schemas live in `scripts/oracle/common.py`.
- **Lean-side emission.** `Hex/Conformance/Emit.lean` provides
  `emitPolyFixture`, `emitMatrixFixture`, `emitLatticeFixture`,
  `emitPrimeFixture`, and `emitResult`. Per-library drivers live
  under `Hex<X>/EmitFixtures.lean` and define a `main`; lakefile
  exposes them as `lean_exe hex<x>_emit_fixtures`. Output goes to
  `stdout` by default, or to the file named by `HEX_FIXTURE_OUTPUT`.
- **Committed sample fixtures.** Each library commits a small
  `conformance-fixtures/Hex<X>/<topic>.jsonl` snapshot so oracle
  drivers can be developed and replayed without re-running Lean. CI
  diffs the freshly-emitted JSONL against the committed file before
  invoking the oracle, so any drift trips the build.
- **Oracle drivers.** `scripts/oracle/<lib>_<oracle>.py`, e.g.
  `scripts/oracle/poly_flint.py`. Drivers reuse
  `scripts/oracle/common.py` for `read_fixtures`, `assert_equal`,
  and `write_failure`. A driver MUST treat a missing oracle import
  as a `SKIP` (exit 0) when the SPEC oracle mode is `if_available`,
  and MUST exit non-zero on any mismatch.
- **Failure records.** On mismatch, the driver writes a JSON record
  to `conformance-failures/<library>-<seed>-<case_id>.json`. The
  directory is gitignored except for a sentinel `README.md`. CI
  uploads any records as a workflow artifact named
  `oracle-<driver>-failures` so the failing case is replayable from
  the recorded input.

### Adding a new oracle

1. Add a per-library emit driver `Hex<X>/EmitFixtures.lean`
   following `HexPoly/EmitFixtures.lean`.
2. Register it as `lean_exe hex<x>_emit_fixtures` in the lakefile.
3. Commit a JSONL snapshot at
   `conformance-fixtures/Hex<X>/<topic>.jsonl` produced by running
   the new driver.
4. Add `scripts/oracle/<lib>_<oracle>.py` mirroring
   `scripts/oracle/poly_flint.py`: it must read the JSONL stream,
   re-run each `op` through the external oracle, and call
   `assert_equal` against the Lean `value`.
5. Wire the new oracle into the **single-ubuntu-job** Conformance
   workflow at `.github/workflows/conformance.yml`. Concretely:
   - if a new system dependency is needed, append it to the existing
     `apt-get install` step;
   - if a new Python dependency is needed, append it to the existing
     `pip install --user` step;
   - append a tuple
     `<lib>|<emit_exe>|<oracle_script>|<fixture_path>` to the
     `ORACLES` array in `scripts/ci/run_oracles.sh`. The runner
     diffs the freshly-emitted JSONL against the committed fixture
     and pipes Lean's emission into the driver per library.

   **Do NOT** add a new top-level workflow job, do **NOT** add a
   `strategy.matrix`, and do **NOT** add a new workflow file. The
   Conformance workflow runs as exactly one ubuntu job — see
   [SPEC/CI.md](CI.md). Conformance failure artefacts are uploaded
   by the workflow's existing `if: failure()` artifact step.

The initial `core` profile does not require JSONL; a library's
`#guard`s suffice until its oracle is wired.

## Sage strategy

Sage is not used as an oracle in this project. Every operation we
want to cross-check has a lighter pip-installable wrapper that
reaches the same FLINT / fpLLL / PARI internals as Sage would:
`python-flint`, `fpylll`, and `cypari2`. Together they cover the
entire oracle surface without a Sage runtime in CI. Local developers
who already have Sage are free to use it ad-hoc, but no CI job
depends on it.

---

This file specifies correctness-oriented cross-checking only.
Performance measurement, complexity-verdict checking, and external
timing comparisons are specified in [benchmarking.md](benchmarking.md).
