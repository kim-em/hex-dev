# DEV.md — hybrid Berlekamp–Zassenhaus migration

> **STATUS: COMPLETE (2026-07).** `Hex.factor` is the cost-based hybrid, it is fast
> (no exponential blow-up on easy inputs), and it is **fully verified**:
> `factor_headline` — product = f ∧ every factor irreducible ∧ normalization ∧
> pairwise-distinct ∧ scalar — is proven **axiom-clean** (`#print axioms` → only
> `propext`/`Classical.choice`/`Quot.sound`), with **zero `sorry`s** in
> `HexBerlekampZassenhausMathlib`. The year-long van Hoeij lattice-soundness blocker
> was closed (#8517). Only optional performance polish remains (#8395, #8382 done).

Roadmap for the migration of `Hex.factor` (the integer polynomial factorizer in
`hex-berlekamp-zassenhaus`) from the BHKS van Hoeij CLD lattice path to a
**cost-based hybrid**. See History for how it landed.

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
| Prove output factors irreducible (the headline) | #8384 | #8412/#8413/#8517 | ✅ **DONE — `factor_headline` axiom-clean, zero sorries** |

The public `factor` now **is** the cost-based hybrid (since #8404): the
exponential-on-easy-inputs blow-up is gone (deg-22 reducible: 781.8 ms → 82.75 ms),
product preservation holds over the hybrid, and the unconditional per-factor
contracts (normalization, primitivity from `f ≠ 0`, pairwise-distinct, scalar)
re-point through the `factorHybrid f = factorizationOfFactors f (factorHybridFactors f)`
bridge. Conformance stands at 100 checks / 0 failures (50 `factor` + 50
`factorClassical`); heavy high-`r` cases (SD4/SD5/Φ₁₀₅) are staged in
`conformance-fixtures/HexBerlekampZassenhaus/bz-scheduled.jsonl`.

---

## The headline — DONE (#8384, closed 2026-07)

`factor_irreducible_of_nonUnit` (every factor `Hex.factor` returns is irreducible)
and the bundled `factor_headline` (product ∧ irreducible ∧ normalization ∧
pairwise ∧ scalar) are **proven over the hybrid, axiom-clean** — `#print axioms`
reports only `[propext, Classical.choice, Quot.sound]`. Zero `sorry`s remain in
`HexBerlekampZassenhausMathlib`. The public factorizer is fully verified and fast.

How it closed (after a year blocked on the lattice route):
- **Reset (#8411):** deleted the ~28k-line BHKS lattice apparatus
  (`Recovery`/`Lattice`/`BadVector`/`TerminationBound`/`CLDColumnBound`/`BHKSBound`/
  `Resultant`/`LiftBridge`/`PartitionRefinement`) — it never closed the headline and
  repeatedly misled agents. Recoverable from `6bf20977^` if ever wanted.
- **Classical route (#8412 → #8413):** the classical search works in the `dilate`
  coordinate and certifies by exact integer division at Mignotte precision, sidestepping
  the CLD lattice soundness entirely; the historically-fatal `exists_subset` quantifier
  is now sign-guarded (the #7550 wall gone). `classicalCoreFactorsWithBound_factor_irreducible`
  landed axiom-clean.
- **Lattice re-verification (#8417 → #8517):** verified the van Hoeij CLD method itself
  (`factorLatticeFactorsWithBound_factor_irreducible`), not an output checker.
- **Assembly (#8414, in #8517):** case-split over the hybrid's three branches; headline
  closed.

Only optional performance polish remains — see Deferred (#8395 lattice speed).

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

### What remains (2026-07)
The headline is proven and closed. The **only** open item is optional performance:
- **#8395** — make the lattice tier *fast* on the SD6+ tail (currently correct but
  slow). **Not shovel-ready:** its body still references the BHKS substrate deleted
  in #8411; it needs a ground-up rewrite. Off the critical path — the classical tier
  covers the whole corpus, so the lattice speed only matters for the extreme-`r` tail.
  Correctness is done regardless (#8517 verified the lattice method).

Everything else in the migration is merged and verified. See History.

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
- **#8382:** classical-tier constant-factor arithmetic speedups (shape-preserving).
- **#8412, #8413 → #8498:** the classical route to the headline. #8412 identified the
  executable candidate with its subset; #8413 proved the classical recombination
  returns irreducible factors (`classicalCoreFactorsWithBound_factor_irreducible`) —
  **axiom-clean** (`#print axioms` → only `propext`/`Classical.choice`/`Quot.sound`).
  The year-long blocker (via the lattice route) is closed via the classical tier
  (`dilate` coordinate, Mignotte precision).
- **#8417, #8414 → #8517:** verified the van Hoeij CLD lattice tier
  (`factorLatticeFactorsWithBound_factor_irreducible` — the *method*, not an output
  checker) and assembled all three branches, **closing the headline
  `factor_irreducible_of_nonUnit`**. `factor_headline` (product ∧ irreducible ∧
  normalization ∧ pairwise ∧ scalar) is proven axiom-clean; zero `sorry`s remain in
  the Mathlib layer. #8538 added a merge-required lattice-tier conformance case.
  **The verified fast factorizer is complete.**
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
    cap-based `factorFast` remains as a proof-facing combinator.
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
up to SD5; the verified-LLL lattice tier handles the extreme-`r` tail (SD6+) where
exhaustive search would explode; the counter gate blocks performance regressions.
**Every correctness contract is proven over the hybrid, axiom-clean:** `factor_headline`
— product = f ∧ each factor irreducible ∧ normalization ∧ pairwise-distinct ∧ scalar
— with zero `sorry`s in `HexBerlekampZassenhausMathlib`. The public factorizer is
fully verified *and* fast. **The migration is complete.**

*Stretch (#8395):* a certificate-backed early-stop would make the lattice tier
fast enough to *strictly beat* the reference on the extreme-`r` tail too (it is
correct-but-slow there today) — needs a ground-up rewrite (its old substrate was
deleted in #8411). The only remaining item, and purely performance; correctness is done.
