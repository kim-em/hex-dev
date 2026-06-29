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

That reframes the goal. We make a **hybrid**: classical recombination for small `r`
(a constant-factor race against the reference) and the verified-LLL van Hoeij CLD
for large `r` (where exhaustive recombination explodes for *everyone*, so the
lattice tier strictly wins). The executable lattice tier (`factorLattice`) stays;
its *proof* substrate (the BHKS lattice apparatus) was reset in #8411 — see
"Next — #8384" for why and the new route. The lattice tier will be re-verified
(#8417), not abandoned.

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

The dispatch is **classical-first** (not an up-front cost estimator), and
**self-certifying**:

```
def factorHybrid f :=                              -- (factorHybridTraced f).1
  match factorClassical f with
  | some φ => if Factorization.product φ = f then φ      -- certified classical answer
              else factorTrial f                          -- (corpus-never) miss → backstop
  | none =>                                               -- classical declined (budget / r too large)
      match factorLattice f with
      | some φ => if Factorization.product φ = f then φ else factorTrial f
      | none   => factorTrial f                           -- no admissible prime
```

Classical-first dominates an up-front `r`-estimate: `factorClassical` peels
reducibles fast and, on irreducibles, exhausts subsets only up to its budget
(~0.26 s worst case) then *declines* cheaply, whereas `factorLattice` grinds to
the precision cap. So we never run the slow tier speculatively — an estimator that
mis-routes a reducible high-`r` input to the lattice would be a disaster.
Each tier's answer is accepted only when it reconstructs the input
(`Factorization.product φ = f`, decidable on `ZPoly`); this is defense-in-depth and
makes product preservation provable now without proving the recombination loop.

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
| CLD lattice tier: certify irreducibility (Swinnerton-Dyer / high-`r`) | #8380 | #8393 | ✅ merged (correctness); speed = #8395 stretch |
| Cost-based hybrid dispatch (classical-first, self-certifying) | #8381 | #8397, #8398 | ✅ merged (`factorHybrid` + `factorHybrid_product`) |
| Classical recombination structurally recursive + reconstruction proved | — | #8401 | ✅ merged (capstone foundation) |
| **Swap public `factor` to the hybrid** (re-point ~100 theorems, both layers) | #8383 | #8404 | ✅ **merged — the public `factor` is now the hybrid** |
| Optimize the easy regime (arithmetic constants) | #8382 | — | ⏸️ deferred — sound part overlaps #8395 (see below) |
| Prove output factors irreducible over the hybrid (the headline `sorry`) | #8384 | — | ⬜ open — long-standing, deep (see below) |

The public `factor` now **is** the cost-based hybrid (since #8404): the
exponential-on-easy-inputs blow-up is gone (deg-22 reducible: 781.8 ms → 82.75 ms),
product preservation holds over the hybrid, and the unconditional per-factor
contracts (normalization, primitivity from `f ≠ 0`, pairwise-distinct, scalar)
re-point through the `factorHybrid f = factorizationOfFactors f (factorHybridFactors f)`
bridge. Conformance stands at 100 checks / 0 failures (50 `factor` + 50
`factorClassical`); heavy high-`r` cases (SD4/SD5/Φ₁₀₅) are staged in
`conformance-fixtures/HexBerlekampZassenhaus/bz-scheduled.jsonl`.

---

## Next — #8384: prove the output factors are irreducible (the headline `sorry`)

The migration is functionally complete: the public `factor` is the hybrid, it is
fast, and its product/normalization contracts are proven. The one remaining *proof*
obligation is `factor_irreducible_of_nonUnit` — every factor `factor` returns is
genuinely irreducible. It is a `sorry` (the long-standing "HO-1 capstone", #4170).

**The route was reset (2026-06).** The old approach proved irreducibility through
the van Hoeij CLD *lattice* in the `scale` coordinate, where it hit a `dilate`-vs-
`scale` mismatch on non-monic inputs and a precision-adequacy gap — blocked for a
year (#7479/#7550/#7561/#8319). **#8411 deleted that entire BHKS lattice apparatus**
(`Recovery`/`Lattice`/`BadVector`/`TerminationBound`/`CLDColumnBound`/`BHKSBound`/
`Resultant`/`LiftBridge`/`PartitionRefinement`, ~28k lines) — it never closed the
headline and repeatedly misled agents into trying to reuse it. It is recoverable
from git (`6bf20977^`) if a specific lemma is ever wanted.

**The new route is the classical tier, and it is unblocked.** The classical search
`scaledRecombinationSmart` works in the **`dilate`** coordinate, where the
correspondence is already proven, and it certifies via exact integer division at
**Mignotte precision** — so it sidesteps the CLD lattice soundness entirely (no
`L=W` / bad-vector argument needed). The historically-fatal `exists_subset`
quantifier is now **sign-guarded** (`normalizeFactorSign factor = factor`), hence
satisfiable — the #7550 wall is gone. The coverage template
(`RecoveredScaledSearch.covers_of_bound`) and the existence/containment/partition
lemmas all survived the deletion. `scaledRecombinationSmart` is structurally
recursive with its reconstruction proven (#8401). So the classical proof is now a
"port the surviving coverage proof to the size-ordered loop" job, like #8401 was.

**Decomposition (shovel-ready issues):**
- **#8412** — identify the executable recombination candidate with its subset
  (`= liftedRecoveryCandidate`); foundation. Care: distinctness of lifted factors
  from the nodup lemmas, not "squarefree ⇒ distinct".
- **#8413** — *the core proof*: the classical search returns irreducibles, via a
  size-ordered coverage induction mirroring `covers_of_bound`. Depends on #8412.
- **#8417** — the lattice branch (the one genuinely hard remainder): prove the
  lattice tier's outputs irreducible, either by re-deriving minimal van Hoeij
  soundness (Route A) or by re-verifying lattice output through #8413's classical
  coverage with a bounded self-certify check (Route B, recommended to evaluate
  first). `factor`'s lattice branch is live (SD6+ tail), so the headline must cover it.
- **#8414** — thin assembly: case-split `factor_irreducible_of_nonUnit` over the
  three branches once each producer (#8413, trial restatement, #8417) exists. Last.

Sequence: #8412 → #8413 → (#8417) → #8414. #8417 is the lone hard branch and can be
sequenced after the rest; do not close the `sorry` with any branch unproven.

---

## Deferred

### #8382 — Constant-factor arithmetic speedups  *(narrowed; fully parallel-safe)*
- **Goal:** close the ~6–9× to Isabelle on small/medium `r` via the low-precision
  bottleneck (`choosePrimeData?`/Berlekamp + per-op `FpPoly`/`DensePoly`/`ZMod64`
  arithmetic).
- **Narrowed (2026-06)** to *output- and shape-preserving* speedups only: same
  factorization outputs (conformance 100/0 and trace 50/0 stay **identical**), and
  no change to any `def` a Mathlib proof unfolds (so it cannot break #8384). That
  makes it fully independent of #8384/#8395 — safe to run in parallel.
- **Moved out to #8395:** the precision-changing levers — incremental-precision
  Hensel lift (~2.6×) and the balanced product-tree multifactor lift.

### #8395 — lattice-tier speed *(needs a full rewrite; substrate deleted)*
Its primary route was a separation certificate `lattice_eq_indicators : L = W` from
`Recovery`/`BadVector`/`TerminationBound` — all **deleted in #8411**. #8395 must be
re-scoped from scratch and is naturally part of the lattice cluster below (a fast,
*and* verified lattice tier are the same substrate problem). Off the critical path.

### Parallelism of the remaining work
- **Track 1 (independent): #8382** — shape-preserving arithmetic constants. Safe in
  parallel with everything.
- **Track 2 (the headline): #8412 → #8413 → #8417 → #8414** — the classical route to
  `factor_irreducible_of_nonUnit`. Independent of #8382; the live path.
- **Track 3 (lattice cluster): #8417 (irreducibility) + #8395 (speed)** — both
  concern the lattice tier and the deleted BHKS substrate; coordinate them. #8417
  depends on #8413 (Route B). Sequence after Track 2's classical core.

### Dispatch readiness (what to start a session on, today)
- **Start now, in parallel:** **#8412** (foundation, no deps) and **#8382**
  (independent perf). Both shovel-ready and self-contained; substrate verified present.
- **Start right after #8412 lands:** **#8413** (the core proof). Shovel-ready but
  gated on #8412 — don't start it cold.
- **Downstream, do not start cold:** **#8417** (needs #8413 + a Route A/B decision)
  and **#8414** (assembly; last step by construction).
- **Do NOT start as written:** **#8395** — its body still points at the BHKS
  substrate deleted in #8411; needs a ground-up rewrite first (re-scope onto whatever
  #8417's route produces).

---

## History (merged)

- **SPEC rewrite (#8375):** hybrid design, counter gate, invariant contracts,
  principle 9.
- **#8376 → #8385:** size-ordered classical recombination (`scaledRecombinationSmart`)
  + hard subset budget + `RecombStats` counters.
- **#8377 → #8386:** `factorClassical` full-domain entry + FLINT invariant op.
- **#8378 → #8387:** adversarial corpus (Swinnerton-Dyer ladder, Mignotte swell,
  cyclotomic, …) + metamorphic relations.
- **#8379 → #8390:** merge-blocking conformance + `FactorTrace` counter gate +
  wall-clock backstop (single ubuntu job, no fan-out); classical declines (`none`)
  on budget exhaustion rather than reporting an untrustworthy "irreducible".
- **#8380 → #8393:** `factorLattice` certifies irreducibility (single all-ones
  partition at the cap → `some #[f]`) on Swinnerton-Dyer / cyclotomic high-`r`
  inputs. *Correct but slow* (grinds to the cap: SD2 14 ms → SD4 deg16 >120 s), so
  it is the **correct fallback** for the extreme-`r` tail; speed is #8395. The
  classical tier already covers everything up to its budget (incl. SD2–SD5) fast, so
  the practical goal is **parity** with Isabelle, lattice as the safety net.
- **#8381 → #8397:** `factorHybrid`/`factorHybridTraced` — classical-first dispatch,
  lattice on decline, trial backstop, traced. (Chose classical-first over the
  directive's up-front cost estimator: classical declines cheaply, lattice grinds.)
- **#8398:** self-certifying hybrid + `factorHybrid_product` (product preservation
  proven unconditionally, no public swap).
- **#8401:** `scaledRecombinationSmart*` made structurally recursive (drop `partial`,
  explicit `fuel`, behavior-identical) + reconstruction proved — the classical-tier
  capstone foundation (steps 1-2).
- **#8383 → #8404:** swapped the public `factor`/`factor?` to the hybrid; added
  `factorHybridFactors` + the `factor f = factorizationOfFactors f (factorHybridFactors f)`
  bridge; re-pointed ~100 `factor`-level theorems across both layers. The conditional
  `h_raw` primitivity hypotheses collapsed to just `f ≠ 0` (the self-certifying
  product reconstruction makes primitivity derivable). Headline irreducibility stays a
  `sorry` (no regression). Easy-input blow-up removed (deg-22: 781.8 ms → 82.75 ms).
- **#8411 (reroute):** deleted the ~28k-line BHKS lattice irreducibility apparatus —
  off the classical route and a repeated trap for agents. Re-homed the headline proof
  to the classical tier (`dilate` coordinate, Mignotte precision, sign-guarded
  `exists_subset`), which sidesteps the year-long `dilate`/`scale` + precision
  blockers. New decomposition: #8412 (candidate↔subset) → #8413 (classical coverage)
  → #8417 (lattice branch) → #8414 (assembly). No proven theorem downgraded; headline
  `sorry` and all live contracts untouched (CI green).

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
    `RecombStats`), `factorClassical` (+ `…WithBound`, `classicalCoreFactorsWithBound`);
  — lattice tier: `factorLattice` (+ `bhksSingleAllOnesPartition`) over the
    `bhks*` / `factorFastCore*` machinery;
  — hybrid (self-certifying): `factorHybrid` / `factorHybridTraced`,
    `factorHybrid_product`, `factorHybridFactors`;
  — public entry (now the hybrid, since #8404): `factor` / `factor?`. The old
    cap-based `factorWithBound` / `factorFast` remain as proof-facing combinators.
- **Reused tiers:** `HexBerlekamp/` (mod-`p` Berlekamp), `HexHensel/` (lift),
  `HexLLL/` (van Hoeij short vectors), `HexPoly*/` (arithmetic).
- **Conformance:** `HexBerlekampZassenhaus/EmitFixtures.lean`,
  `scripts/oracle/bz_flint.py`, `scripts/ci/run_oracles.sh`,
  `conformance-fixtures/HexBerlekampZassenhaus/{bz.jsonl, bz-scheduled.jsonl}`.
- **Bench / reference:** `HexBerlekampZassenhaus/Bench.lean`, `HexBench/`,
  the cached Isabelle wrapper under `.cache/oracles/bz-isabelle/`,
  `reports/bz-classical-spike-findings.md`.
- **Mathlib (proof) layer:** `HexBerlekampZassenhausMathlib/{Basic,IntReductionMod,
  FactorSoundness}.lean` — the live surface: the classical-route substrate
  (`liftedRecoveryCandidate`, `RecoveredScaledSearch.covers_of_bound`, the
  sign-guarded `exists_subset`), `factor_product` / normalization, and the headline
  `sorry`. The BHKS lattice apparatus (`Recovery`/`Lattice`/`BadVector`/
  `CLDColumnBound`/`BHKSBound`/`Resultant`/`LiftBridge`/`TerminationBound`/
  `PartitionRefinement`) was **deleted in #8411**; recover from `6bf20977^` only if a
  specific lemma proves wanted for the lattice re-verification (#8417).

---

## End state

Public `factor` is the cost-based hybrid (since #8404): it reaches **parity** with
the verified Isabelle reference on every input the classical tier covers —
everything up to the classical subset budget, including the Swinnerton-Dyer ladder
up to SD5; the verified-LLL lattice tier is a **correct fallback** for the
extreme-`r` tail (SD6+) where exhaustive search would explode; the counter gate
blocks performance regressions; product and normalization contracts are proven over
the hybrid. The open proof is the headline irreducibility (#8384) — now routed
through the classical tier (#8412/#8413/#8414) with the lattice branch (#8417) the
lone hard remainder. (#8382's easy-regime constants are a later polish, not required
for parity.)

*Stretch (#8395):* a certificate-backed early-stop would make the lattice tier
fast enough to *strictly beat* the reference on the extreme-`r` tail too — needs a
ground-up rewrite (its old substrate was deleted in #8411). Not on the critical path.
