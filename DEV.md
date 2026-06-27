# DEV.md — hybrid Berlekamp–Zassenhaus migration

Living roadmap for the in-progress migration of `Hex.factor` (the integer
polynomial factorizer in `hex-berlekamp-zassenhaus`) from the BHKS van Hoeij CLD
lattice path to a **cost-based hybrid**. Update the status section as issues land.

This is a development tracker, not a spec: the timeless design lives in
[`SPEC/Libraries/hex-berlekamp-zassenhaus.md`](SPEC/Libraries/hex-berlekamp-zassenhaus.md)
(and `…-mathlib.md`), and the governing principle in
[`SPEC/design-principles.md`](SPEC/design-principles.md) (principle 9).

---

## Why this migration

The current public `factor` is **exponential on easy reducible inputs**. The cause
is a *dispatch* bug, not the math: it runs a low-precision-cap van Hoeij CLD
attempt that "misses", then falls through to exhaustive 2ⁿ subset recombination.
On `(x−1)…(x−24)` it takes ~3 s; it hits an 8 s cap by degree ~15.

We verified (by reading the AFP source under
`.cache/oracles/bz-isabelle/afp/.../Berlekamp_Zassenhaus/Reconstruction.thy`) that
the verified Isabelle reference `factor_int_poly` reconstructs via **classical
exhaustive `subseqs` recombination — no LLL/lattice** — with fast constants
(GHC + Karatsuba). So Isabelle is *exponential in the modular-factor count `r`*,
just with a fast constant: deg-32 Swinnerton-Dyer (`r≈16`) ≈ 40 ms; deg-64
(`r≈32`) does not finish in minutes.

That reframes the goal. Rather than delete the BHKS work, we make a **hybrid**:
classical recombination for small `r` (a constant-factor race against the
reference) and the verified-LLL van Hoeij CLD for large `r` (where exhaustive
recombination explodes for *everyone*, so the lattice tier strictly wins). The
prior BHKS soundness work is preserved as the large-`r` tier.

Background measurements: [`reports/bz-classical-spike-findings.md`](reports/bz-classical-spike-findings.md).

---

## Architecture (the end state)

Three result-equivalent recombination tiers share one front end
(normalise → choose prime → Hensel lift) and differ only in how they recombine
the lifted mod-`p` factors:

- **`factorClassical`** — size-ordered subset recombination with factor removal
  under a hard **subset budget**. Same algorithm class as Isabelle; the win is
  arithmetic constants. `O(2^r)` worst case. Used for small `r`.
- **`factorLattice`** — van Hoeij CLD via the verified `hex-lll`. Polynomial in
  `r`. Used when `r` is large enough that classical search would blow its budget.
- **`factorTrial`** — exhaustive integer trial division; the total totality
  backstop, reached only when no admissible prime exists.

```
def factor f :=
  match choosePrimeData? f with
  | none   => factorTrial f                      -- no admissible prime
  | some d =>
      match dispatchTier f d with                -- COST estimate, not a precision cap
      | .classical => factorClassical f <|> factorLattice f <|> factorTrial f
      | .lattice   => factorLattice f  <|> factorClassical f <|> factorTrial f
```

`dispatchTier` estimates cost from `r`, the modular factors' degree distribution,
coefficient height / Mignotte precision, the expected size-ordered subset count,
and the CLD lattice dimension; near the threshold it may re-choose the prime to
get a smaller `r` (`r` depends on the prime, not on `f` alone).

**Gating goal, by regime:** match Isabelle on small/medium `r`; **strictly beat**
it on large `r` (Swinnerton-Dyer class).

---

## Correctness philosophy (design principle 9)

Correctness is established **primarily by conformance + benchmarking**, and the
formal proofs land **last and adapt to the committed implementation** — never the
reverse. We have thrashed too often bending the implementation to ease proofs.

- **Conformance (merge-blocking):** differential testing against FLINT
  (`scripts/oracle/bz_flint.py`) over an adversarial corpus, with independent
  invariant checks (product = input, primitivity, positive leading coefficient,
  multiplicities, per-factor irreducibility) plus metamorphic relations
  (`f` vs `−f` vs `content·f` vs `f(X+k)`; multiply-then-factor; different-prime →
  same result).
- **Performance (merge-blocking):** a counter + wall-clock gate. `factor` exposes
  a `FactorTrace` (chosen tier, prime, `r`, Hensel precision, subset count,
  lattice dimension, **fallback-used**). The gate asserts on the *counters*, not
  just elapsed time — a pure timing gate is gameable (a regression can "pass" by
  silently falling back to a slow tier, or by only timing out off-CI). This is the
  guard that prevents replacing the implementation with something exponentially
  slower "so that it can be verified".
- **Proofs (deferred, last):** keep the BHKS proofs (the lattice tier); prove the
  classical tier (largely the existing slow-path / Group A proofs) + dispatch
  soundness + tier-equivalence; re-target the headline correctness theorem over
  the hybrid. No `axiom`s ever.

---

## Status

| Item | Issue | PR | State |
|---|---|---|---|
| SPEC rewrite (hybrid design, counter gate, contracts, principle 9) | — | #8375 | ✅ merged |
| Size-ordered classical recombination + subset budget + counters | #8376 | #8385 | ✅ merged |
| `factorClassical` full-domain entry + FLINT invariant op | #8377 | #8386 | ✅ merged |
| Adversarial corpus + metamorphic relations | #8378 | #8387 | ✅ merged |
| Merge-blocking conformance + counter + wall-clock gate (+ budget soundness) | #8379 | #8390 | ✅ merged |
| CLD lattice tier: certify irreducibility (Swinnerton-Dyer / high-`r`) | #8380 | — | ⬜ next (unblocked); root cause diagnosed |
| Cost-based `dispatchTier` | #8381 | — | ⬜ blocked on #8379, #8380 |
| Optimize the easy regime (arithmetic constants) | #8382 | — | ⬜ blocked on #8379 |
| Swap public `factor` to the hybrid | #8383 | — | ⬜ blocked on #8380, #8381, #8382 |
| Re-prove headline + dispatch soundness over the hybrid | #8384 | — | ⬜ blocked on #8383 |

Everything merged so far is **purely additive**: the public `factor` is unchanged
until #8383, so `main` stays stable while the tiers are built and validated.
Conformance currently stands at 100 checks / 0 failures (50 `factor` + 50
`factorClassical`) on the per-PR corpus; heavy high-`r` cases (SD4/SD5/Φ₁₀₅) are
staged in `conformance-fixtures/HexBerlekampZassenhaus/bz-scheduled.jsonl`.

---

## Remaining issues (detail)

### #8379 — Merge-blocking conformance + counter + wall-clock gate
- **Goal:** make "can't quietly regress to something slower" enforceable.
- **Work:** thread a `FactorTrace` (tier, `p`, `r`, Hensel precision, subset count,
  lattice dim, fallback-used) through the factor path; add one CI step (extend the
  *single* ubuntu job per `SPEC/CI.md` — no fan-out) that runs the corpus under
  generous wall-clock caps and asserts per-fixture counters (expected tier, no
  unexpected trial fallback, subset count ≤ bound) against a committed baseline
  JSON; wire a scheduled run for `bz-scheduled.jsonl`.
- **Verify:** gate passes on the current corpus; deliberately slowing a tier or
  forcing a fallback fails it locally.
- **Risk:** infra-heavy (CI YAML + counter probe + baseline). The `FactorTrace`
  scaffold may sit on `factorClassical` until the dispatch lands.

### #8380 — CLD lattice tier: certify irreducibility (Swinnerton-Dyer / high-`r`)
- **Goal:** make `factorLattice` return `some #[f]` (not `none`) on irreducible
  high-`r` inputs, so the dispatcher can route Swinnerton-Dyer-class inputs to it
  instead of the exponential exhaustive fallback.
- **Root cause (diagnosed 2026-06):** the "miss" is **not** a cap/precision bug and
  the lattice is **not** broken. `bhksRecoverClassified` (Basic.lean ~6747)
  correctly finds the single all-ones equivalence class for an irreducible input,
  but `bhksDegenerateIndicatorPartition` treats that — a *correct irreducibility
  proof* — as `degenerate → none`. Measured: `bhksRecover?` / `factorFast` return
  `none` at every precision up to the (10²¹⁺) cap on SD2/SD3/Φ₁₅. This was right
  for the old fall-back-to-slow architecture; it is wrong for the hybrid, where
  the lattice tier must certify irreducibility itself.
- **Work:** add an irreducibility **stopping criterion** — at the cap
  (`k ≥ bhksBound`), classify the all-ones single-class partition as `success #[f]`
  rather than `degenerate` (keep declining at sub-cap precision); expose the
  lattice-dimension counter; validate via the FLINT oracle + counter gate on the
  SD/cyclotomic corpus (those inputs are irreducible, so `[f]` is correct).
- **Open question (not a blocker):** *speed*. The localized fix makes the tier
  **correct**; whether it is fast enough to strictly beat Isabelle's exponential
  on the SD ladder needs a clean benchmark (the earlier ">90s" was a
  wrong-precision probe artifact). If too slow, reassess (lattice/LLL optimization
  vs accept parity-via-classical).
- The kept BHKS proofs (Recovery/Lattice/CLDColumnBound/BadVector/…) and the
  cap-suffices proof (BHKS Thm 5.2 / D1, deferred per principle 9) live here.

### #8381 — Cost-based `dispatchTier`
- **Goal:** the hybrid router.
- **Work:** `dispatchTier f d` estimator from `r` + modular degree distribution +
  coefficient height + expected subset count + lattice dim; near-threshold bounded
  multi-prime retry keeping the smallest `r`; the combinator classical → lattice →
  trial, recording the `FactorTrace`, flagging unexpected fallback. Kept **off**
  the public `factor` (behind `factorHybrid`) and gated by #8379.
- **Risk:** threshold tuning; the multi-prime retry; getting the counter
  assertions exactly right.

### #8382 — Optimize the easy regime  *(parallel; only needs #8379)*
- **Goal:** close the ~6–9× to Isabelle on small/medium `r`.
- **Work:** incremental-precision Hensel lift with Mignotte backstop (~2.6×) +
  balanced product-tree lift; speed up `choosePrimeData?`/Berlekamp (the dominant
  low-precision cost); re-measure on the scheduled ratio; record the baseline.
- **Risk:** touches shared arithmetic — guarded by conformance; may not fully
  close the gap (parity is the target, not a strict win on easy inputs).

### #8383 — Swap public `factor` to the hybrid  *(first behavior-changing change)*
- **Goal:** make the cost-based hybrid the real entry point; retire the cap-based
  three-tier.
- **Work:** point `factor`/`factor?` at `dispatchTier` (#8381); all conformance +
  counter + wall-clock gates green; update `Conformance.lean` expectations and the
  baseline JSON.
- **Risk:** the first non-additive public change; the gate must be solid. After
  this, the exponential-on-easy-inputs bug is gone and hard inputs route through
  the lattice tier.

### #8384 — Re-prove over the hybrid  *(the big proof unknown; deferred by design)*
- **Goal:** restore formal correctness on the new `factor`.
- **Work:** prove the classical tier (Group A, promoted) + dispatch soundness +
  tier equivalence; re-target the headline theorem (`factor_product`,
  `factor_irreducible_of_nonUnit`) over the hybrid; keep Group B/D1 (lattice tier).
- **Risk:** largest effort, but conformance + benchmark already establish
  correctness; proofs adapt to the implementation (principle 9). The existing
  slow-path proofs likely carry most of the classical tier.

---

## Order and parallelism

```
#8379 ──┬─► #8380 ──► #8381 ──► #8383 ──► #8384
        └─► #8382 ──────────────►┘
```

**Critical path:** #8379 → #8380 → #8381 → #8383 → #8384.  **#8382** runs in
parallel after #8379. (Alternative: tackle #8380 first to de-risk the CLD tier
before building the gate/dispatch around it.)

---

## Execution workflow

Each issue, in `depends-on` order:

1. Branch off `main`.
2. Implement; keep `lake build` green per commit; `#guard`s for unit checks.
3. Run the FLINT conformance gate:
   `lake exe hexbz_emit_fixtures | python3 scripts/oracle/bz_flint.py`
   (and, from #8379, the counter/wall-clock gate; and the scheduled bench where
   relevant).
4. PR (`<type>: <subject>`, prose body, ends `🤖 Prepared with Claude Code`);
   squash-merge; sync `main`; take the next unblocked issue.

Never bend the implementation to a future proof. Never introduce an `axiom`.
`native_decide` is banned. CI stays one ubuntu job, no fan-out (`SPEC/CI.md`).

---

## Key files and pointers

- **SPEC:** `SPEC/Libraries/hex-berlekamp-zassenhaus.md`, `…-mathlib.md`,
  `SPEC/design-principles.md` (principle 9), `SPEC/CI.md`, `SPEC/benchmarking.md`.
- **Executable factorizer:** `HexBerlekampZassenhaus/Basic.lean`
  — front end: `normalizeForFactor`, `reassemblePolynomialFactors`,
    `choosePrimeData?`, `henselLiftData`;
  — classical tier: `scaledRecombinationSmart` (+ `subsetsOfSizeWithComplement`,
    `RecombStats`), `factorClassical` (+ `…WithBound`, `classicalCoreFactorsWithBound`,
    `recombineScaledSmart`);
  — lattice tier (to harden): the `bhks*` / `factorFastCore*` machinery;
  — public entry (to swap in #8383): `factor`.
- **Reused tiers:** `HexBerlekamp/` (mod-`p` Berlekamp), `HexHensel/` (lift),
  `HexLLL/` (van Hoeij short vectors), `HexPoly*/` (arithmetic).
- **Conformance:** `HexBerlekampZassenhaus/EmitFixtures.lean`,
  `scripts/oracle/bz_flint.py`, `scripts/ci/run_oracles.sh`,
  `conformance-fixtures/HexBerlekampZassenhaus/{bz.jsonl, bz-scheduled.jsonl}`.
- **Bench / reference:** `HexBerlekampZassenhaus/Bench.lean`, `HexBench/`,
  the cached Isabelle wrapper under `.cache/oracles/bz-isabelle/`,
  `reports/bz-classical-spike-findings.md`.
- **The kept BHKS proofs** (large-`r` tier): `HexBerlekampZassenhausMathlib/`
  (`Recovery.lean`, `Lattice.lean`, `CLDColumnBound.lean`, `BadVector.lean`,
  `PartitionRefinement.lean`, `Resultant.lean`, `BHKSBound.lean`,
  `TerminationBound.lean`, `FactorSoundness.lean`).

---

## End state

Public `factor` is the cost-based hybrid: it ties the verified Isabelle reference
on easy inputs (after #8382), strictly beats it on hard (Swinnerton-Dyer) inputs
via the verified LLL, the counter gate blocks performance regressions, and the
headline correctness theorem is restored (after #8384). The BHKS work is
preserved as the large-`r` tier, not deleted.
