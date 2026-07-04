# Rewrite of the real-roots / rcf SPECs (replaces PR #2656's drafts)

## Accomplished

Reviewed https://github.com/kim-em/hex-dev/pull/2656 with Kim and
rewrote the three planned-library SPECs from scratch on branch
`spec/real-roots-and-rcf`, superseding the PR's Descartes-only
design. The review found the PR's completeness theorem
(`isolate?_succeeds_at_separation_precision`) unprovable as stated:
Descartes variation counts are disturbed by nearby non-real roots
(witness `(x − 1)² + ε²`), so a real-gap separation bound cannot
drain the worklist, and the missing classical ingredient (the
Obreshkoff two-circle theorem) is formalised nowhere. Kim rejected a
soundness-only fallback and chose a hybrid design:

- `SPEC/Libraries/hex-real-roots.md`: isolation witnesses are Sturm
  counts (exact, half-open `(a, b]` convention with zero-skipping
  variations). Two engines over one self-certifying output type:
  a Descartes search (fast, no proof obligations) and a Sturm
  bisection (provably drains at `isolationDepth`, which is derived
  from complex-root separation). `isolate?` runs Descartes first,
  Sturm on fallback. Chain is the primitive
  positive-multiplier pseudo-remainder sequence (no hex-resultant
  dependency, no Sylvester-Habicht sign bookkeeping). Root bound is
  Cauchy (Mathlib-proved), not LMQ. Conformance must assert the
  Descartes engine alone succeeds on every fixture, with a standing
  rule that the PR proving `isolateDescartes?_isSome` deletes those
  assertions.
- `SPEC/Libraries/hex-real-roots-mathlib.md`: Sturm's theorem as a
  self-contained upstreamable slice over `Polynomial ℝ`, chain
  correspondence, `isolate?_isSome` (full completeness, no deferred
  dependency), root identity via `Quot` over interval overlap
  (mirroring the revised hex-roots conventions). The two-circle
  theorem is specified as the one deferred strengthening; nothing
  else waits on it.
- `SPEC/Libraries/hex-rcf.md`: two-level reflected language
  (quantifier-free `Formula` under a single-quantifier `Sentence`),
  total decision through `isolate?_isSome`, root-cell signs via
  Sturm counts of `gcd(pⱼ, P)`, separation and endpoint-alignment
  refinement before cell construction, and kernel replay via a
  certificate (`check`/`check_sound`) following the
  `irreducible_cert` compiled-prep / kernel-verify pattern. No bench
  target (Mathlib import ban); no `hex-rcf-mathlib`.

Registered all three in `libraries.yml` (`status: planned`),
extended `SPEC/Libraries/README.md` (lists, dependency section,
index, six-to-nine SPEC count), added the `RCF` token to
`scripts/libgraph.py`. `scripts/check_dag.py` passes. Style pass
done against `SPEC/writing-style.md` (no em-dashes, no banned
words, run-on semicolons split).

## Current frontier

The branch is ready for Kim's review as a replacement for PR #2656
(that PR is CONFLICTING against main and describes the abandoned
Sturm-only/`hex-sturm` design in its title and body).

## Next step

Kim reviews the diff; open a fresh PR from
`spec/real-roots-and-rcf` and close #2656 in favour of it. When
implementation starts, the Sturm chain and counting slice is the
natural first work item (everything else certifies against it).

## Blockers

None. The deferred two-circle theorem is scoped so that no other
obligation waits on it.
