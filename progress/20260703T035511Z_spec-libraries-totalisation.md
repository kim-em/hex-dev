# Totalisation redesign for the SPEC/Libraries/ specs

Follow-up to `20260703T024028Z_spec-libraries-review.md`, after Kim
rejected the fuel-based drivers and proposed junk-valued total
arithmetic.

## Accomplished

Replaced the fuel design across hex-roots.md, hex-roots-mathlib.md,
hex-number-field.md, hex-number-field-mathlib.md with the design Kim
and I converged on:

- hex-roots: termination is structural after all. The worklist holds
  uncertified `Component` values (squares + candidateK); a subdivision
  round is total (`T_0`-discard keeps children it cannot certify
  empty, which is sound), and the measure
  `Φ = Σ (#squares) · 5^(gap)` strictly decreases per round.
  Certification (`Component.certify?`) happens only when producing
  output, escalating past the target to
  `stopDepth p target = max target (separationDepth p) + c₀`, with
  `separationDepth p = mahlerPrec p + c₁` computable Mathlib-free.
  `none` from the drivers now has exactly one meaning: a Pellet
  witness failed to appear at separation depth. `atomize` became
  total (the k = 1 cluster witness already lives on the enclosing
  square).
- hex-roots-mathlib: completeness item is now
  `certifies_by_separationDepth` (plus `isolate ≠ none` corollary),
  a statement about depths and witnesses with no recursion counter.
- hex-number-field: user-facing arithmetic (`add`, `mul`, `sub`,
  `neg`, `inv`, `toAlgebraicNumber`) is total. Internal `?`-forms
  return `Option`; the public wrappers pin the `none` branch to `0`
  via a new `Hex.panicWith (v : α) (msg : String) : α` (explicit junk
  value per Kim; loud at runtime, definitionally `v`). Junk `0` needs
  `isIrreducible X` to reduce in the kernel, so `isIrreducible` gets
  a degree-1 fast path. `QAdjoin.approx` is total with a sound
  fallback (the current disc's ball, wider than requested).
  `commonField?` keeps the informative Option signature
  (algorithm-layer). The two library-specific loop bounds are named:
  `disambiguationPrec` (height/resultant lower bound on wrong-factor
  values) and `maxShift` (conjugate-pair collision count).
- hex-number-field-mathlib: theorems staged as `?_sound`
  (certificate correct; provable without completeness), `?_isSome`
  (bound sufficiency; item 6, deferrable with hex-roots
  completeness), and unconditional headlines like
  `(α.add β).toComplex = α.toComplex + β.toComplex` by composition.
  `approx_sound` is unconditional; only `approx_radius` waits on
  completeness.

Checked: no "fuel" remains, no em-dashes/banned vocabulary, names
consistent across the four files. All changes still uncommitted
(along with the previous turn's), awaiting Kim's diff review.

Final-review addendum (same session): a fresh read caught a
soundness gap in the driver design as written: a rootless component
(whose `T_0` tests merely failed at the current depth) can certify
`k = 1` through disc overlap with a neighbour, double-counting that
root. Fixed by requiring the output clusters' witness discs to be
pairwise disjoint (a dyadic per-pair check, the analogue of BSSY §4's
separation condition); hex-roots-mathlib's IsolateAll soundness and
completeness item 11 updated to match. Also: renamed the pinned
constants to `stopSlack`/`sepSlack` (they collided with the Taylor
coefficients `c₀`, `c₁`), and pinned `inv 0 = 0` (Mathlib's division
convention) so `inv` takes no hypothesis.

## Current frontier

Spec set is consistent under the totalisation design. `panicWith` and
`isIrreducible` are the two small cross-library additions
(HexNumberField/Basic.lean for now, and hex-berlekamp-zassenhaus
respectively).

## Next step

Kim reviews the combined diff; then commit. Implementation order
unchanged: hex-resultant, hex-roots, hex-number-field.

## Blockers

None.

## Second addendum (same session): Kim's four follow-up concerns

1. **Slack constants**: pinned `sepSlack = stopSlack = 8` in
   hex-roots.md, with the argument for why a uniform constant
   suffices (each subdivision level doubles the isolation ratio past
   `mahlerPrec`, so the analysis can only need a handful of levels,
   independent of the input; overshoot costs a few extra rounds).
2. **`disambiguationPrec`**: spelled out the explicit formula in
   hex-number-field.md (coprime factors give `|Res(m,g)| ≥ 1`; the
   root-product formula plus Landau bound each conjugate; everything
   reads off the factor list). Formal ingredients are all
   already-verified Mathlib API.
3. **Kernel decide**: measured on the v4.32.0-rc1 toolchain with a
   list-based model (scratchpad kernel_decide_test.lean): a
   degree-10/F₅ Rabin-style workload kernel-reduces in ~0.7 s inside
   default limits; an oversized degree-20/F₁₃ workload takes ~46 s
   with raised maxRecDepth/maxHeartbeats. Risk reduced by giving
   `isIrreducible` a four-rung ladder (canonical-form check for
   degree 1; rational-root test for degree ≤ 3; mod-p Rabin for a few
   small primes; full factor fallback, runtime-only in practice),
   documented in hex-number-field.md with the companion obligations
   (mod-p lifting lemma).
4. **Rouché status re-verified**: Mathlib mainline (2026-06-18) has
   no argument principle / Rouché / residue theorem; open PRs are two
   stalled residue drafts (#29588, #39232); Junyan Xu's étale-space
   programme (#31925) targets general contours, not needed here. But
   for polynomials on circles the hard ingredients EXIST:
   `circleIntegral.integral_sub_inv_of_mem_ball`,
   `DiffContOnCl.circleIntegral_eq_zero`,
   `Polynomial.derivative_prod`,
   `continuous_parametric_intervalIntegral_of_continuous`. Items 5-7
   of hex-roots-mathlib.md rewritten: partial fractions + linearity +
   the two integrals give the polynomial argument principle; Rouché
   by integer-valued-continuous homotopy. Also recorded the
   MeromorphicOn decoupling trap (LeanEval's rouche_zero_count_eq was
   false for this reason; Zulip 2026-05): everything stays on
   `Polynomial ℂ`.
