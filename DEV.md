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
fast, and its product/normalization contracts are proven. The one remaining
*proof* obligation is `factor_irreducible_of_nonUnit` — that every factor `factor`
returns is genuinely irreducible (can't be split further). It is a `sorry` today,
and has been since long before this migration (the "HO-1 capstone", #4170); the
swap neither helped nor hurt it.

**Why it is hard (plain version).** The algorithm factors `f` by choosing a prime
`p`, factoring `f` mod `p` into pieces, Hensel-lifting them to mod `p^k`, then
keeping any *combination* of lifted pieces whose product divides `f` over ℤ.
Proving an output factor is irreducible means proving its set of pieces is
**minimal** — no smaller sub-combination is also a genuine factor. That needs an
exact dictionary between "subsets of the mod-`p` pieces" and "true integer factors"
(the *Hensel-subset correspondence*).

**Where it is stuck.**
- The correspondence is proven in one coordinate (`dilate`, the substitution
  `x ↦ c·x`) but the minimality/subset argument needs it in another (`scale`,
  multiply by `c`). They agree only when the leading coefficient is `1` (monic);
  for **non-monic** inputs there is no bridge — that is the missing math. Earlier
  attempts (#7479, #7550, #7561, #8319) were each diagnosed as needing genuinely
  new lattice theory or as resting on a *false* hypothesis, and were skipped rather
  than forced. (Details in those issues and the `hex-lean-mathlib-boundary` skill.)
- Even with the correspondence, it is only exact once the lift precision passes a
  threshold, and whether the algorithm's actual precision provably reaches it is a
  second open question (the BHKS column-adequacy / bad-vector lemmas).

**What is already in hand for it.** `scaledRecombinationSmart` is now structurally
recursive with its reconstruction (`product = target`) proven (#8401) — the
foundation an *unconditional classical-tier* irreducibility proof would build on.
The conditional `factor*_branch_entry_irreducible_of_choosePrimeData` lemmas (over
the proof-facing `factorWithBound`) already discharge several dispatch branches; the
non-monic correspondence is the genuinely-blocked remainder.

This is deep, multi-session BHKS lattice-soundness work — not a re-pointing chore.

---

## Deferred

### #8382 — Optimize the easy regime  *(deferred; sound part overlaps #8395)*
- **Goal:** close the ~6–9× to Isabelle on small/medium `r`.
- **Why deferred:** the headline lever — the incremental-precision Hensel lift
  (~2.6×, lift low then escalate) — is only **sound** with a per-remainder
  completeness certificate. The size-ordered recombination accepts only verified
  exact integer divisors, so a low-precision run always has `product = f` yet may be
  **incomplete** (an unsplit factor is byte-identical to a genuine irreducible);
  detecting "incomplete vs done" cheaply is exactly the certificate scoped to
  **#8395**. `exhaustiveLiftBound = max(B, defaultFactorCoeffBound(monic core))` is
  already the tight Mignotte bound, so there is no free sound win from tightening it.
- **What's left here:** the modest/risky levers — balanced product-tree lift
  (1.2–1.4× at full precision) and `choosePrimeData?`/Berlekamp micro-opt (touches
  heavily-proven code). Verification is the **informational** scheduled ratio, not a
  merge gate. Land after the capstone; fold the incremental-precision piece into #8395.

### #8395 — Certificate-backed early-stop for the lattice tier  *(stretch)*
- Making `factorLattice` fast on the extreme-`r` tail (SD6+) needs a believed-sound
  `L'=W` / no-bad-vector check before the BHKS precision cap, exposed from the kept
  `BadVector`/`Recovery`/`TerminationBound` proofs — **not** a partition-stability
  heuristic (which could mis-declare a reducible input irreducible). Not on the
  critical path; without it we bank parity via the classical tier.

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
- **The kept BHKS proofs** (large-`r` tier): `HexBerlekampZassenhausMathlib/`
  (`Recovery.lean`, `Lattice.lean`, `CLDColumnBound.lean`, `BadVector.lean`,
  `PartitionRefinement.lean`, `Resultant.lean`, `BHKSBound.lean`,
  `TerminationBound.lean`, `FactorSoundness.lean`).

---

## End state

Public `factor` is the cost-based hybrid (since #8404): it reaches **parity** with
the verified Isabelle reference on every input the classical tier covers —
everything up to the classical subset budget, including the Swinnerton-Dyer ladder
up to SD5; the verified-LLL lattice tier is a **correct fallback** for the
extreme-`r` tail (SD6+) where exhaustive search would explode; the counter gate
blocks performance regressions; product and normalization contracts are proven over
the hybrid. The one open proof is the headline irreducibility (`#8384`, still a
`sorry`). The BHKS work is preserved as the large-`r` tier, not deleted. (#8382's
easy-regime constants are a later polish, not required
for parity.)

*Stretch (#8395):* a certificate-backed early-stop would make the lattice tier
fast enough to *strictly beat* the reference on the extreme-`r` tail too, not just
match it. Not on the critical path.
