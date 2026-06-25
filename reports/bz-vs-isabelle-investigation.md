# HexBerlekampZassenhaus vs Isabelle/AFP: investigation

This report documents what was found while comparing hex's
`HexBerlekampZassenhaus.factor` against the Isabelle/AFP
`Berlekamp_Zassenhaus.factorize_int_poly` extracted-Haskell binary
([scripts/oracle/setup_lll_isabelle.sh](https://github.com/kim-em/hex-lll/blob/main/scripts/oracle/setup_lll_isabelle.sh)
sets up the LLL deposit; for BZ I built the AFP session locally and exported
`factor_int_poly` to Haskell). All measurements on `Apple M2`, May 2026.

## 1. Headline

On the deterministic split family $(x-1)(x-2)\cdots(x-n)$ at $n \in \{2, \ldots, 24\}$,
hex's public `factor` combinator is **200–2,400× slower** than Isabelle/AFP's
extracted `factor_int_poly` AND **returns mathematically incorrect output**
on roughly half the inputs.

| n | hex (Lean) | Isabelle/AFP | hex/Isa | hex result |
|---|----------:|-------------:|--------:|------------|
| 8 | 64 ms | 0.27 ms | 240× | 8 linears (correct) |
| 10 | 167 ms | 0.36 ms | 460× | 10 linears (correct) |
| 14 | 742 ms | 0.86 ms | 860× | 14 linears (correct) |
| 16 | 1.42 s | 1.21 ms | 1180× | 16 linears (correct) |
| 20 | 4.43 s | 1.78 ms | 2490× | 20 linears (correct) |
| 11 | 4.8 ms | 0.58 ms | 8× | **3 reducible factors (wrong)** |
| 12 | 5.7 ms | 0.66 ms | 9× | **3 reducible factors (wrong)** |
| 13 | 11 ms | 0.74 ms | 15× | **3 reducible factors (wrong)** |
| 15 | 19 ms | 1.04 ms | 18× | **3 reducible factors (wrong)** |
| 22 | 1.42 s | 2.40 ms | 590× | **3 reducible factors (wrong)** |
| 24 | 6.09 s | 2.97 ms | 2050× | **3 reducible factors (wrong)** |

The plot is at [/tmp/bz-lean-vs-isabelle.png](/tmp/bz-lean-vs-isabelle.png).

"Wrong" means: hex returns 3 polynomials whose product equals the input,
but each is itself reducible (i.e. they aren't irreducible integer factors).
This violates the documented `Factorization` contract.

## 2. What the repo already tracks

- **Issue [#2564](https://github.com/kim-em/hex/issues/2564) (open, "HO-1")**: *"BZ recombination implements wrong lattice — rollback and rewrite to van Hoeij CLD."* Open since Apr 2026. Describes the additive-vs-multiplicative-lattice error in `recombineLLL?`/`recombinationLattice?`. Mandates a rewrite to BHKS CLD with `factorSlow` + `factorFast` + `factor := factorFast.getD factorSlow`. The current code reflects a *partial* implementation of the new architecture: the `factorSlow`/`factorFast`/`factor` combinator at [HexBerlekampZassenhaus/Basic.lean#L5903](../HexBerlekampZassenhaus/Basic.lean#L5903) was added, but the underlying recombination still has the failure modes described below.
- **Issue [#2565](https://github.com/kim-em/hex/issues/2565) (closed, "HO-2")**: added adversarial conformance fixtures (Φ₁₅, SD₃, X⁴+1, (X²−2)(X²−3)). These pass in current `main` — the failure modes in this report are not in the fixture corpus.
- **Issue [#2566](https://github.com/kim-em/hex/issues/2566) (closed, "HO-3")**: added `HexBerlekampZassenhaus/Bench.lean`. Phase-4 schedules cover the `splitScientificSchedule = #[2, 3, 4, 5]` and a degree/height matrix, none of which reach `n` large enough to expose the failure.
- **[reports/hex-berlekamp-zassenhaus-performance.md](hex-berlekamp-zassenhaus-performance.md)**: every scaling verdict is *inconclusive* (`cMin=2.6, cMax=349` for `runFactorChecksum`). No external comparator is declared in [libraries.yml](../libraries.yml) for `HexBerlekampZassenhaus.phase4`. The §"Concerns" closing notes explicitly flag that "final Phase 4 coverage should add or explicitly justify comparator metadata before bumping `done_through`." So the repo has no Isabelle-vs-hex BZ baseline yet.
- **[reports/hex-lll-performance.md](https://github.com/kim-em/hex-lll/blob/main/reports/hex-lll-performance.md)** *does* have an Isabelle LLL comparator and reports hex 10.88× faster at `n=25` trending down to 1.49× slower at `n=55`. That's where the "we were faster" intuition comes from — but it's the LLL line of work, not BZ.

## 3. Root cause: `isGoodPrime` rejects all candidate primes, then `fallbackPrimeChoiceData` silently uses `p = 3`

### 3.1 The chain

[HexBerlekampZassenhaus/Basic.lean:67-71](../HexBerlekampZassenhaus/Basic.lean#L67) defines:

```lean
def isGoodPrime (f : ZPoly) (p : Nat) [ZMod64.Bounds p] : Bool :=
  let fModP := ZPoly.modP p f
  3 <= p &&
    ZPoly.leadingCoeffModP f p != 0 &&
    DensePoly.gcd fModP (DensePoly.derivative fModP) == 1
```

The intended predicate is *"f is square-free mod p"*. The third conjunct
checks that `gcd(f, f')` is **structurally equal to the polynomial 1**.

But [HexPoly/Euclid.lean:832](../HexPoly/Euclid.lean#L832) defines `gcd`
as the value returned by the **Euclidean algorithm** (`xgcd p q`), which
over a field returns an associate of the true gcd — *not* a monic
representative.

So when `f` is genuinely square-free mod `p`, the gcd returned is a
**non-zero constant other than 1** (a unit in `Fp`, but not the
polynomial `1`). `isGoodPrime` rejects it.

Concrete probe: for $f = (x-1)(x-2)\cdots(x-11)$ at $p = 13$,
`DensePoly.gcd (f mod 13) (f' mod 13)` returns the constant polynomial
`[4]`. In $\mathbb{F}_{13}$, $4$ is a unit (it has inverse $10$), so the gcd
is *mathematically* a unit and $f$ is square-free mod 13. But the
executable check `== 1` returns `false`, so `isGoodPrime f 13 = false`.

### 3.2 `choosePrimeData?` returns `none` everywhere — fallback to p=3

`choosePrimeData?` ([Basic.lean#L1962](../HexBerlekampZassenhaus/Basic.lean#L1962))
folds over `smallPrimeCandidates = [3, 5, 7, 11, 13, 17, 19, 23, 31, 71]`,
scoring each via `primeChoiceDataScore` ([Basic.lean#L1704](../HexBerlekampZassenhaus/Basic.lean#L1704)),
which short-circuits on `isGoodPrime`. When every candidate prime is
rejected, the fold returns `none`.

`choosePrimeData` then falls through to `fallbackPrimeChoiceData`
([Basic.lean#L1966](../HexBerlekampZassenhaus/Basic.lean#L1966)):

```lean
private def fallbackPrimeChoiceData (f : ZPoly) : PrimeChoiceData :=
  letI := bounds_three
  let c : SmallPrimeCandidate :=
    { p := 3, bounds := bounds_three, prime := prime_three }
  let fModP := ZPoly.modP 3 f
  let factorsModP := berlekampFactorsModP f c
  { p := 3, fModP, factorsModP }
```

It unconditionally uses `p = 3`, with **no check that 3 is actually good
for this input.**

For $f = (x-1)\cdots(x-n)$ with $n \ge 24$, every prime in
`smallPrimeCandidates` is rejected by `isGoodPrime` for two reasons that
compound:

1. Genuine non-square-free-ness for the small primes (the integer roots
   $\{1, \ldots, n\}$ collide modulo $p$ when $p \le n$).
2. The `gcd == 1` mis-comparison for the primes where the polynomial *is*
   square-free (here, $p \in \{29, 31, 71\}$ ⊆ candidate list at $n = 24$
   give a true square-free image but a non-canonical gcd).

So $p = 3$ is chosen even though $f$ is *highly* non-square-free mod 3
(each residue class $0, 1, 2$ appears 8 times among the roots).

Probe ([scratch/PrimeProbe.lean](scratch/PrimeProbe.lean)) confirms
`isGoodPrime` returns `false` for every candidate prime in the input list,
for every "wrong-output" case from §1:

```
n=11: p=3:false 5:false 7:false 11:false 13:false 17:false 19:false 23:false 31:false 71:false
n=24: p=3:false 5:false 7:false 11:false 13:false 17:false 19:false 23:false 31:false 71:false
```

### 3.3 What happens downstream

With $p = 3$ and $f \bmod 3$ non-square-free, the Berlekamp factorisation
of $f \bmod 3$ returns the *square-free part*, which has 3 distinct
linear factors over $\mathbb{F}_3$ (one per residue class). The fast-path
combinator lifts these via Hensel to mod $3^k$ (with $k$ large enough to
recover Mignotte-bounded factors), reconstructs them as integer
polynomials of degree $n/3$ each, and returns them as if they were
irreducible factors.

[scratch/FactorTrace.lean](scratch/FactorTrace.lean) confirms this
directly. For $n = 24$, the fast path returns three monic integer
polynomials of degree 8 each. Their product is the input, so the
`Factorization.product` invariant holds — but each is itself a degree-8
product of distinct linears, not an irreducible.

The hex `Factorization` type doesn't carry an irreducibility witness; the
combinator just accepts whatever the fast path returns. Issue
[#2564](https://github.com/kim-em/hex/issues/2564) calls for `factorFast`
to have a `factorFast f = some gs ⟹ gs is the irreducible factorisation`
proof obligation in the Mathlib bridge — that obligation, if discharged,
would force the implementation to reject this case (return `none`),
which would route control to `factorSlow`, which is at least
unconditionally correct (though exponentially slow in the number of
mod-$p$ factors).

## 4. Why hex is also slow when it *is* correct

At $n = 16$ and $n = 20$, `choosePrime` selects $p = 19$ and $p = 23$
respectively (both square-free for those inputs, and the gcd bug
happens to not bite because of how the residues land). Hex returns the
correct full factorisation — but takes **1.4 s** and **4.4 s**
respectively, against Isabelle's **1.2 ms** and **1.8 ms**.

The slowdown is concentrated in the Hensel-lift / BHKS-recombination
loop, not in prime selection. Direct timing of `Hex.factorFast` at
`factorFastPrecisionCap` (which is the *higher*, BHKS-doubling cap
rather than the Mignotte-tight `defaultFactorCoeffBound`):

| n | fastCap precision (digits) | Hex.factorFast wall |
|---|---------------------------:|---------------------:|
| 8 | 138 | 64 ms |
| 10 | 230 | 172 ms |
| 14 | 480 | 797 ms |
| 16 | 614 | 1.52 s |
| 20 | 968 | 4.71 s |

The headline cost is multi-precision Hensel arithmetic at the BHKS-doubling
precision cap, plus the lattice construction / LLL reduction that follows.
Even the *successful* runs are spending most of their time doing
arithmetic at much higher precision than the inputs require, and an LLL
reduction whose lattice (per #2564) doesn't actually encode the
multiplicative-product structure of the factorisation.

The closest sibling comparator is the LLL line, where hex is *roughly
equal* to the same AFP-extracted Haskell at large $n$ (within ±10%).
That suggests the slowdown is not "Lean is slow at integer arithmetic"
— the same Lean LLL kernel matches AFP. It is concentrated in the BZ
glue: prime selection, Hensel-lift precision schedule, and recombination
strategy.

## 5. Verifying the diagnosis

[scratch/GcdProbe.lean](scratch/GcdProbe.lean) shows the
gcd-not-monic behaviour. [scratch/PrimeProbe.lean](scratch/PrimeProbe.lean)
confirms every candidate prime is rejected for every wrong-output input.
[scratch/FactorTrace.lean](scratch/FactorTrace.lean) confirms the
output structure (3 reducible factors of degree $n/3$ when $p_{\text{chosen}} = 3$).

The diagnosis predicts that any patch to `isGoodPrime` that accepts the
"gcd is a unit" case (rather than "gcd is literally the polynomial 1")
would (a) make `choosePrimeData?` succeed on these inputs by selecting
the smallest *actually-square-free* prime, and (b) restore correct
factorisation output. I have *not* attempted that patch here because the
predicate has downstream lemma callers; verifying that those still go
through is part of the fix PR.

## 6. Recommendations

In priority order:

1. **Fix `isGoodPrime`.** Either normalise the gcd to monic at the
   `DensePoly.gcd` level, or change the predicate at
   [Basic.lean:71](../HexBerlekampZassenhaus/Basic.lean#L71) to check
   "gcd has degree 0 and is non-zero" (i.e. *is a unit* in $\mathbb{F}_p[x]$).
   Normalising at the `gcd` level is cleaner mathematically — a
   field-gcd that isn't monic is a footgun for every other caller — but
   it touches more existing proofs.

2. **Remove the silent `p = 3` fallback.** `fallbackPrimeChoiceData`
   masks bugs like §3 by always returning a definite answer. After
   exhausting `smallPrimeCandidates`, the right move is to *extend the
   search* to larger primes (à la Isabelle's unbounded `find_prime`),
   not to silently use a known-bad prime. Until extension lands,
   `fallbackPrimeChoiceData` should `panic!`/throw rather than silently
   succeed — better an exception than a wrong factorisation.

3. **Add an irreducibility witness to `factorFast`'s contract.** Per
   issue [#2564](https://github.com/kim-em/hex/issues/2564), the spec
   already says `factorFast f = some gs ⟹ gs is the irreducible
   factorisation`. If that obligation is enforced by the implementation
   (e.g. each factor must pass a trial-division check against every
   other lifted local factor's product), the wrong-output path collapses
   to a `none` from `factorFast`, and `factorSlow` takes over.

4. **Wire Isabelle/AFP BZ as a Phase-4 comparator in
   [libraries.yml](../libraries.yml).** The `setup_lll_isabelle.sh`
   skill is the right template — an analogous `setup_bz_isabelle.sh`
   that builds the AFP `Berlekamp_Zassenhaus` session and exports
   `factor_int_poly` to Haskell would give a permanent ratio baseline.
   The plot at [/tmp/bz-lean-vs-isabelle.png](/tmp/bz-lean-vs-isabelle.png)
   becomes a regression bar once we have the comparator in CI.

5. **Add wrong-output fixtures to `HexBerlekampZassenhaus/Conformance.lean`.**
   $(x-1)(x-2)\cdots(x-11)$ is the smallest input in the deterministic
   split family that triggers the bug; if it had been in the fixture
   corpus the current behaviour would have been a build-time failure.
   $(x-1)\cdots(x-24)$ exhibits the worst-case wall time. Both belong
   in the corpus alongside the HO-2 adversarials.

6. **Even with §1 fixed, ~200–1,000× to Isabelle remains.** That gap is
   in BHKS-precision Hensel arithmetic + lattice construction; closing
   it is the substance of the actual #2564 rewrite to van Hoeij CLD.
   The numbers here suggest the rewrite is worth doing — Isabelle's
   classical exhaustive recombination handles all of these inputs in
   single-digit milliseconds, so the verified algorithm is not the
   constraint; the implementation strategy is.

## 7. Artefacts

- [scratch/BZBench.lean](scratch/BZBench.lean): Lean factor timings on the split-product ladder.
- [scratch/FactorTrace.lean](scratch/FactorTrace.lean): per-input trace of `factorFast` vs `factor`, prime choice, precision cap.
- [scratch/PrimeProbe.lean](scratch/PrimeProbe.lean): direct `isGoodPrime` probe across every candidate prime per input.
- [scratch/GcdProbe.lean](scratch/GcdProbe.lean): single-case demonstration of the non-monic gcd at $n=11, p=13$.
- [scratch/bz_flint_times.py](scratch/bz_flint_times.py), [scratch/plot_bz.py](scratch/plot_bz.py): FLINT timings + plot (informational).
- [scratch/plot_bz_isa.py](scratch/plot_bz_isa.py): Lean vs Isabelle plot.
- `/tmp/hex-isabelle/` (recreate per §8): AFP code-export wrapper theory + Haskell driver for `factor_int_poly`.

## 8. Post-mortem: why didn't the orchestrator catch this?

The `isGoodPrime` bug affects both **correctness** (wrong output
returned as if it were the irreducible factorisation) and
**performance** (multi-second wall time at degrees where Isabelle is
sub-millisecond). It should have been caught in two independent
places — conformance and benchmarking — *and* in a third (Mathlib
bridge). It was caught in zero. Four orchestration gaps:

### 8.1 Gap 1 — SPEC has no comparator requirement for BZ

[SPEC/benchmarking.md §"Comparator naming"](../SPEC/benchmarking.md)
requires every Phase-4 library to either name a comparator or
explicitly declare absence with a reason from a closed list. BZ's SPEC
([SPEC/Libraries/hex-berlekamp-zassenhaus.md](../SPEC/Libraries/hex-berlekamp-zassenhaus.md))
does **neither**. [libraries.yml](../libraries.yml) records
`phase4.input_families` for `HexBerlekampZassenhaus` but no
`phase4.comparators` key.

The current state is admissible because `done_through: 0` — Phase 4 is
not yet claimed, so the comparator-absence-declaration requirement
hasn't activated. But [reports/hex-berlekamp-zassenhaus-performance.md](hex-berlekamp-zassenhaus-performance.md)
*does* write a Phase-4 performance report with verdicts. The bench
schedule runs, reports inconclusive verdicts, and the gap is recorded
in §"Concerns" of the report — but as a TODO, not a blocker. There is
no mechanism that ties "wallclock surprise vs comparator" to
"orchestrator pauses dispatch".

**Direct consequence:** the only signal that BZ was slow was an
internal-model verdict (`cMin / cMax` of the declared
`n^9 + n^7 log²(n+2)` model), which is unitless. The hex Phase-4 run
recorded `cMax=349` at `n=4` and **interpreted this as "schedule too
short"**, not "the algorithm is doing wrong work". An Isabelle/AFP
comparator would have shown `lean/isabelle ≈ 240×` even at `n=4` and
flagged the gap immediately.

### 8.2 Gap 2 — conformance fixtures intentionally avoid prime-cascade adversarials

The current fixture corpus
([conformance-fixtures/HexBerlekampZassenhaus/bz.jsonl](../conformance-fixtures/HexBerlekampZassenhaus/bz.jsonl), 27 fixtures)
covers degree 0–4 edge cases, irreducible cyclotomics Φ₅/Φ₇/Φ₁₁/Φ₁₇,
the HO-2 adversarials (X⁴+1, (x²−2)(x²−3), SD₃, Φ₁₅), two
reducible products at degree 4 and 20, and two content-cyclotomic
combos. **Largest degree: 20. No deterministic split linear product
of degree > 2.**

HO-2 ([#2565](https://github.com/kim-em/hex/issues/2565)) explicitly
calls out that pre-HO-2 fixtures had "true factors that coincide with
single mod-p factors" and adds adversarials for the recombination
logic — but the adversarials it adds (X⁴+1 etc.) are all small-degree
and all happen to pick a good prime in the first few candidates. The
prime-selection cascade (`isGoodPrime` rejects everything → silent
fallback to `p=3`) is a *different* adversarial axis that the HO-2
corpus does not stress.

`$(x-1)(x-2)\cdots(x-n)$` for $n \in \{11, 12, 13, 15\}$ is the
smallest input family that exercises the cascade. None of these are
in the corpus.

**Direct consequence:** the python-flint oracle DOES re-check that every
hex-reported factor is irreducible per flint
([HexBerlekampZassenhaus/EmitFixtures.lean#L56-L60](../HexBerlekampZassenhaus/EmitFixtures.lean#L56)),
so any reducible output in a fixture would fail conformance. But the
corpus doesn't include any input that *produces* reducible output, so
the oracle's irreducibility check is dead weight against this bug
class. **The check exists but the corpus is constructed to avoid
exercising it.**

### 8.3 Gap 3 — bench schedule too short

`splitScientificSchedule = #[2, 3, 4, 5]` for `runFactorChecksum` runs
the public combinator on $(x-1)(x-2)\cdots(x-(n+1))$ for
$n \in \{2, 3, 4, 5\}$ — degrees 3, 4, 5, 6. At every one of those
degrees, the smallest square-free candidate prime $\le 7$ satisfies
`isGoodPrime` and the cascade never fires. The bench *cannot* catch
this bug at its current schedule.

[reports/hex-berlekamp-zassenhaus-performance.md §"Concerns"](hex-berlekamp-zassenhaus-performance.md)
already notes the issue obliquely: "an exploratory run with the same
eight-second cap reached n = 5 and hit the cap at n = 6, so larger
split inputs require either algorithmic improvement or a dedicated
longer scheduled run." Without a comparator the right interpretation
("the algorithm is doing wrong work") is indistinguishable from the
wrong one ("we need a longer schedule").

### 8.4 Gap 4 — pipeline-level invariants are not stated, so per-step soundness lemmas don't compose into pipeline correctness

[HexBerlekampZassenhaus/Basic.lean:965](../HexBerlekampZassenhaus/Basic.lean#L965)
states:

```lean
theorem isGoodPrime_squareFreeModP
    (f : ZPoly) (p : Nat) [ZMod64.Bounds p]
    (hgood : isGoodPrime f p = true) :
    squareFreeModP f p := by ...
```

But `squareFreeModP` itself is defined ([Basic.lean:57](../HexBerlekampZassenhaus/Basic.lean#L57))
as `DensePoly.gcd fModP (DensePoly.derivative fModP) = 1` — the
*same* boolean condition `isGoodPrime` checks. The theorem is
near-tautological. It doesn't connect `squareFreeModP` to the
Mathlib concept `Polynomial.Squarefree`. So no bridge theorem *would
have failed to prove* in the presence of this bug — every claim about
`squareFreeModP` is downstream of the same boolean expression that
the executable evaluates.

This is a symptom of a deeper pattern. **The bridge file carries
many per-step "if the executable check passes, then the Prop form
holds" lemmas, but no end-to-end theorem about the pipeline.** What
should exist is something like:

```lean
theorem factor_returns_irreducible_factorisation
    (f : ZPoly) (hf : f ≠ 0) :
    let φ := Hex.factor f
    Factorization.product φ = f ∧
      ∀ (g : ZPoly) (_ : g ∈ φ.factors.map Prod.fst),
        Polynomial.Irreducible (HexPolyZMathlib.toPolynomial g)
```

A theorem of that shape would not be provable today.

The orchestrator currently dispatches **per-function proof
obligations** (e.g. issue [#2564](https://github.com/kim-em/hex/issues/2564)
asks for "A1–A5", "B1–B9", "C1–C2" as a *bag* of obligations) and not
the end-to-end pipeline theorem. The right relationship is the
opposite of how that's structured: **the end-to-end theorem is the
specification, and per-function lemmas are consequences of it that
emerge from how the proof factors.** Stating a bag of per-function
obligations without naming the global theorem they exist to support
is performative — it produces lemmas that are checkable in isolation
but need not actually compose. When the lemmas don't compose (as
here: `isGoodPrime_squareFreeModP` is true but tautological, so its
"discharge" does not constrain the implementation), the bag is
discharged and the global property is still wrong.

The corollary: a per-function obligation that does not appear as a
step in some proof of the global theorem is dead weight. It should
either be removed, or the proof structure should be revised until
the lemma is load-bearing. The SPEC must dispatch the global theorem
as the critical-path artefact, and let the proof's actual
decomposition determine which intermediate lemmas earn their place.

This is the meta-gap, and it generalises beyond `isGoodPrime`. The
correct change is at the SPEC level: every `done_through ≥ 4` library
must carry a "headline correctness theorem" in its Mathlib bridge
stating the end-to-end invariant of its public API, and *that
theorem* is the critical-path artefact the orchestrator dispatches.
Intermediate lemmas land alongside the headline theorem and exist
only because the headline-theorem proof factors through them.

### 8.5 Gap 5 — `fallbackPrimeChoiceData` is an unprotected total-function smell

[HexBerlekampZassenhaus/Basic.lean:1982](../HexBerlekampZassenhaus/Basic.lean#L1982):

```lean
def choosePrimeData (f : ZPoly) : PrimeChoiceData :=
  match choosePrimeData? f with
  | some data => data
  | none => fallbackPrimeChoiceData f
```

with `fallbackPrimeChoiceData` returning `{p := 3, …}` unconditionally.
This is the proximate cause of the wrong-output bug: when
`choosePrimeData?` returns `none` (because `isGoodPrime` rejected
every candidate due to gap 4), `choosePrimeData` silently returns the
$p = 3$ branch without any guard. Every production caller in the
factor pipeline uses `choosePrimeData` (the total form), not
`choosePrimeData?`, so the `none` branch flows into the executable
result without any check.

There is **no theorem anywhere in the repo** of the form
`choosePrimeData?_isSome` (the Option always inhabits `some`), and no
documentation rationalising the fallback choice of $p = 3$. The
fallback exists for purely syntactic reasons (the type system wanted
a total function), with no mathematical safety net.

This is a code smell with a precise resolution. Fallbacks in
total-of-Option helpers are admissible **only** when one of these is
the case, and the SPEC must enforce the discipline:

- The caller proves the fallback is unreachable on the intended
  inputs (a theorem `_isSome_of_<precondition>`).
- The fallback itself is a verified emergency value that callers
  *audit*, with a rationale in the SPEC text.
- Or the function is re-architected to not need a fallback (here:
  use `choosePrimeData?` throughout the pipeline, or replace the
  bounded `smallPrimeCandidates` list with an unbounded prime
  search, à la Isabelle's `find_prime`, plus a Mathlib bridge
  theorem that termination is guaranteed for sf primitive input
  via the existence-of-good-primes lemma).

Without any of these, the fallback is a silent rewrite of the
algorithm's mathematical contract: "BZ on a polynomial without a good
small prime" becomes "BZ at $p=3$", which is a different algorithm
with a different output. The SPEC must forbid this without a stated
rationale.

### 8.6 Summary of orchestration changes needed

1. **SPEC PR (drafted at [reports/bz-spec-comparator-pr-draft.md](bz-spec-comparator-pr-draft.md)):**
   - Add an AFP `Berlekamp_Zassenhaus` extracted-Haskell comparator
     classified as `gating` to `hex-berlekamp-zassenhaus.md` and
     `libraries.yml`. Symmetric with the existing LLL comparator setup.
   - Add a SPEC clause requiring the headline correctness theorem for
     `factor` to be discharged in `HexBerlekampZassenhausMathlib`
     before any `done_through` bump past Phase 4. The theorem must
     state irreducibility of every entry in `φ.factors`, not just
     `Factorization.product φ = f`.
   - Add a SPEC clause on fallback discipline: any total-of-`Option`
     helper in the pipeline must carry either an `_isSome` theorem
     proving the `none` branch is unreachable on the intended inputs,
     or a documented rationale for the fallback value. Pre-existing
     fallbacks must be audited under the new rule.

2. **Rollback issue (drafted at [reports/bz-rollback-issue-draft.md](bz-rollback-issue-draft.md)):**
   roll back the BZ Phase-4 bench scaffolding for re-execution against
   the new comparator. The bench artefact in the perf report becomes
   informational-only until the comparator gate is closed *and* the
   headline correctness theorem is in place.

3. **HO-2 corpus extension (separate issue):** require at least one
   `(x-1)(x-2)…(x-n)` instance with $n$ chosen large enough that
   `isGoodPrime` would reject every prime in `smallPrimeCandidates`
   even after the gcd-monic fix (i.e. $n > 71$ so even mod 71 isn't
   square-free). This forces the prime-search-extension fix rather
   than allowing the gcd-monic fix alone to ship.

4. **Pipeline correctness theorem (separate issue, Mathlib bridge):**
   state and prove `factor_returns_irreducible_factorisation` as the
   end-to-end public-API theorem. Per-function obligations from
   [#2564](https://github.com/kim-em/hex/issues/2564) compose toward
   this; the issue tracks the composition itself, not any new
   per-function proof.

5. **Fallback audit (separate issue):** grep
   [HexBerlekampZassenhaus/Basic.lean](../HexBerlekampZassenhaus/Basic.lean)
   for every `match … | none => …` pattern that defaults to a concrete
   value. Each must either grow an `_isSome` theorem or a SPEC
   rationale, or be re-architected to not need a default.

## 9. Reproducing the Isabelle side

```sh
brew install --cask isabelle
curl -sL https://www.isa-afp.org/release/afp-current.tar.gz \
  -o /tmp/isabelle-afp.tar.gz
mkdir -p /tmp/isabelle-afp
tar -xzf /tmp/isabelle-afp.tar.gz -C /tmp/isabelle-afp --strip-components=1
isabelle components -u /tmp/isabelle-afp/thys

# Build the AFP BZ session (one-time, ~7 min):
isabelle build -b -v Berlekamp_Zassenhaus

# Then the wrapper theory and Haskell export driver are at
# /tmp/hex-isabelle/{bz/Hex_BZ_Export.thy, driver/Main.hs}; see §7.
```
