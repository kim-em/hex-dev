---
name: hex-lean-mathlib-boundary
description: Gotchas for the Mathlib-free/Mathlib boundary in HexBerlekampZassenhausMathlib and similar *Mathlib Lean layers (ZMod64, FpPoly, DensePoly, ZPoly). Read before proving lemmas that mix the executable types with Mathlib Polynomial / ZMod algebra, OR before verifying any change to a *Mathlib bridge file — CI does not build those libraries, so a whole-library `lake build` failure may be pre-existing on main (see "The Mathlib layer is not CI-built").
allowed-tools: Bash, Read, Grep, Glob
---

# Mathlib-free / Mathlib boundary in the hex Lean layers

The executable types (`Hex.ZMod64 p`, `Hex.FpPoly p = Hex.DensePoly (ZMod64 p)`,
`Hex.ZPoly = Hex.DensePoly Int`) carry **only `Lean.Grind` ring instances and a
custom `Dvd`** — *not* Mathlib's `CommRing`/`Field`/`Monoid`/`AddGroup`
typeclasses. Mathlib homomorphism lemmas therefore fail to synthesize instances
on these types. Do arithmetic with `grind`, and cross to the Mathlib
`Polynomial (ZMod p)` / `ZMod p` side through the project's bridges.

## Concrete rules

- **`grind`, not `ring`, for `ZMod64`/`FpPoly` arithmetic.** Ring lemmas
  (`mul_one`, `neg_add_cancel`, `ring`) need Mathlib instances these types lack.
  `grind` uses the `Lean.Grind.CommRing` instance; prime-inverse facts
  (`ZMod64.inv_mul_eq_one_of_prime`, `mul_inv_eq_one_of_prime`) are `@[grind]`.
- **No `map_neg` / `map_one` / `map_zero` / `map_dvd` on `ZMod64`/`FpPoly`.**
  These need `ZeroHomClass`/`AddMonoidHomClass`/`Monoid` that the executable
  types don't have. To compute e.g. `toZMod (-1) = -1`: prove `(-1)+1 = 0` in
  `ZMod64` by `grind`, push through `toZMod_add`/`toZMod_one`/`toZMod_zero`
  (the real bridge lemmas), and finish in `ZMod p` with
  `eq_neg_of_add_eq_zero_left`.
- **`FpPoly`/`DensePoly` `∣` is custom** (`a ∣ b := ∃ r, b = a * r`), so
  `map_dvd` does not apply and `dvd_trans` is replaced by `fpPoly_dvd_trans`.
  Transport divisibility to Mathlib by destructuring and re-multiplying:
  `obtain ⟨r, hr⟩ := h; ⟨toMathlibPolynomial r, by rw [hr, toMathlibPolynomial_mul]⟩`.
  (`HexBerlekampZassenhausMathlib/Basic.lean` exposes `toMathlibPolynomial_dvd`
  and `self_dvd_monicModPImage` for exactly this.)
- **`ZMod64` zero has two representations** (`Zero.zero` vs `OfNat 0`); a `rw`
  on `toZMod 0` / `(0 : FpPoly).coeff n` may report "did not find pattern" or
  leave an unclosed `0 = 0`. Close with `exact`/`show` (defeq-tolerant), not
  `rw`/`simp`.
- **`HexPolyMathlib.toPolynomial` vs `HexPolyZMathlib.toPolynomial`:**
  `HexPolyZMathlib.toPolynomial` is an `abbrev` specializing the general
  `HexPolyMathlib.toPolynomial` to `R = Int`. They are defeq but **not
  syntactically equal**, so `rw [hk]` fails when `hk` was produced by a
  `HexPolyMathlib`-namespace lemma against a `HexPolyZMathlib` goal. Bind the
  result with an explicit `HexPolyZMathlib.toPolynomial …` type ascription
  first, then `obtain`/`rw`.

## Proving *inside* the Mathlib-free files

Lemmas that live in the executable files themselves (`HexPoly/*`,
`HexPolyZ/*`, `HexBerlekampZassenhaus/Basic.lean`) cannot use Mathlib tactics
or `Monoid`/`CommRing` lemmas — those modules don't import Mathlib.

- **`by_contra`, `ring`, `omega`-via-Mathlib are out.** `by_contra` reports
  "unknown tactic"; replace with `rcases Nat.eq_zero_or_pos n` or
  `rcases Nat.lt_trichotomy a b`. `omega`/`simp`/`rcases`/`conv` are core and
  available.
- **Integer `^` has no `pow_add`/`pow_succ`/`pow_one`/`one_pow` (Mathlib).**
  Use `Lean.Grind.Semiring.pow_succ` (`a^(n+1) = a^n * a`) and
  `Lean.Grind.Semiring.pow_zero`; `Int.one_pow`, `Int.mul_assoc`,
  `Int.mul_comm`, `Int.mul_zero`, `Int.one_mul` are core and fine. For
  `a^(m+k) = a^m * a^k`, write a one-line induction on `k` with `pow_succ`.
- **`omega` does not see through `Int.ofNat`.** It normalizes the `↑n` /
  `Nat.cast` coercion but treats the explicit constructor `Int.ofNat n` as an
  opaque atom — so `0 ≤ Int.ofNat n` and `Int.ofNat n.natAbs = n` (with
  `0 < n`) both fail with a bogus counterexample. `content`/`contentNat`
  (`HexPoly/Euclid.lean`) are defined via `Int.ofNat`, so Gauss/content proofs
  hit this. Either restate the goal as `(n : Int)` (Nat.cast, which `omega`
  handles) and close by `exact` up to defeq, or use core lemmas directly:
  `Int.natAbs_of_nonneg`, `Int.mul_pos`, `Nat.pos_of_ne_zero`. Note
  `Int.ofNat_pos` does **not** exist.
- **Array/List core lemma names differ from intuition:** the lemma for
  `(l.toArray).toList = l` is `List.toList_toArray` (not `Array.toList_toArray`).
  For `(xs.push a).getD`, `HexBerlekampZassenhaus/Basic.lean` already has
  `array_getD_push_lt`/`array_getD_push_size`/`array_toList_getD` — reuse them.

## Signature gotcha

A hypothesis whose type mentions `toMathlibPolynomial`/`monicModPImage`/`modP`
at `primeData.p` is elaborated **before** any `letI := primeData.bounds`, so an
implicit `[Bounds primeData.p]` cannot be synthesized and the type silently
becomes `sorry`. Write the instance explicitly in such signatures:
`@HexBerlekampMathlib.toMathlibPolynomial primeData.p primeData.bounds (…)`.

## The Mathlib layer *models* executable definitions

The bridge does not just prove lemmas about the executable types; it carries
**model definitions that mirror the shape of executable functions** —
e.g. `scaledRecombinationCandidate` / `scaledLiftedFactorProduct` /
`RepresentsIntegerFactorAtLift` (`HexBerlekampZassenhausMathlib/Basic.lean`)
mirror the per-step candidate built inside `Hex.scaledRecombinationSearchModAux`
/ `bhksIndicatorCandidate?`. Before changing an executable definition's *shape*
(the candidate expression, the recombination target, the lift transform),
grep the Mathlib layer for proofs that `unfold` it or restate its body, and
size that surface first — it is often far larger than the executable proofs.

Two directions behave very differently under such a change:

- **Product / divisibility direction survives.** Proofs like `*_product` rest
  on the `exactQuotient? target candidate` recursion, which is blind to how the
  candidate was built, so they need only mechanical `let`-expression updates
  (mirror the new candidate text) — never a new argument.
- **Recovery / coverage direction does not.** Proofs that identify the emitted
  candidate against an expected factor (the `RepresentsIntegerFactorAtLift`
  recovery chain, the coverage proof in `Basic.lean`) *encode* the old shape;
  changing it is a structural remodel needing new math, not a token swap. These
  feed the still-`sorry` headline `factor_irreducible_of_nonUnit`, but they are
  proven (not sorried) lemmas, so they must still compile.

Consequence: a soundness fix to the executable recombination is **not**
independently landable green — the executable change and the Mathlib remodel
must land in one PR. Scope accordingly (see #6799 / #6801 for the
`DensePoly.scale` → `ZPoly.dilate` example).

**Size the migration before deep-reading proofs.** When a predicate like
`RepresentsIntegerFactorAtLift` flips from being *defeq* to a recovery equality
(e.g. the scaled `reduceModPow` congruence) to wrapping a *structure*
(`Nonempty (RecoveredAtLift …)`), every consumer that fed `hrep` into a recovery
lemma breaks, and the dilate bridge (`RecoveredAtLift.candidate_eq_of_monic_dvd`)
needs a *different precision/bound model* than the consumers carry — the bound
moves from the factor to the monic-coordinate witness (`(toMonic core).monic`),
plus `hmonic_ne` / `hfactor_norm`. That new hypothesis cascades through every
caller up to the top driver (where `(toMonic core).monic = core` collapses it).
So before sinking a session into per-theorem reads: for each erroring consumer,
`grep -n "<name>_of_bound\b"` the **caller fan-out**. If a forced signature
change hits more than a handful of callers (each re-cascading), it is a
multi-session remodel with no intermediate green state — land the cascade-free
fixes (e.g. a `2 ≤ d.p^k` derivable straight from precision +
`defaultFactorCoeffBound_pos_of_ne_zero`, not from a recovery lemma), then
partial + scope the rest in one accurately-sized follow-up rather than
attempting the whole cascade blind. Watch for a hidden soundness signal too:
the new `RecoveredAtLift.dilate_eq` carries no `normalizeFactorSign`, so a
`0 < leadingCoeff factor` conclusion is only valid for sign-normalised factors —
the consumer must gain `hfactor_norm`, which callers do supply.

When you reroute the broken scale-model consumers off the removed scale
congruence, **do not target the `hdilated` exact-equality chain**
(`candidatesOfDilatedCenteredLift` / `ofMignottePrecisionCandidateProducts`),
even though the issue body may name it. That chain's `hdilated` wants the
*exact* `dilate (lc f) (centeredLiftPoly …) = expectedFactor` with **no**
`primitivePart`, but `RecoveredAtLift.dilate_eq` only ever gives the
`primitivePart (dilate (lc core) monicFactor) = factor` form, and that
`primitivePart` is load-bearing: `coeff_dilate` is `coeff n = c^n · p.coeff n`
(`HexPolyZ/Basic.lean:70`), so `dilate 4 (x+2) = 4·x + 2` has `content = 2`.
Hence `content (dilate (lc core) monicFactor) = 1` is **false** whenever
`leadingCoeff core` is a non-unit — i.e. the generic non-monic-core regime the
monic transform exists for. Reroute to the primitivePart-aware
`liftedRecoveryCandidate` / `RecoveredAtLift.candidate_eq_of_monic_dvd`
(`Basic.lean:2781`) path instead. And note the linchpin: there is **no base
`RecoveredAtLift` producer** built from a successful `bhksIndicatorCandidate?`
(every theorem concluding `RepresentsIntegerFactorAtLift` is a packer or
hypothesis-consumer); constructing one — the `dilate_eq`/`monic_dvd` carrier
from the executable candidate — is the monic-transform recovery direction owned
by the fast-BHKS-monic-lift migration issue, so a scale→dilate consumer reroute
is blocked on that producer landing first.

### "Final integration" issues: confirm the substrate *producer* exists, not just that the feeder issue closed

A `feature` issue that says "instantiate `SlowPathHenselSubstrate` / `…Evidence`
constructed by the prerequisite issues" is only a token-swap if a theorem
*concludes* that structure. A closed feeder issue does **not** prove its
producer landed: these substrate issues are sometimes closed COMPLETED on a
replan-triage comment whose claim contradicts the source (e.g. #6773 was closed
asserting `liftedFactorSubsetPartition_of_choosePrimeData` "does not assume" the
evidence, but it takes `hinitial : InitialLiftedFactorSubsetPartitionEvidence`
as a hypothesis and only projects fields out of it). Before claiming such an
integration, grep for an actual producer: `grep -rn ": <StructureName>"` should
find a `theorem … : <StructureName> …` whose body builds it (or a `{ field := … }`
literal), not just `(h : <StructureName>)` binders and `…_fields h` projections.
If every occurrence is a hypothesis or destructor, the substrate is unproduced —
diagnose on the issue (per the CLAUDE.md "Directives are hypotheses" rule) and
`coordination skip` rather than attempting the integration. The big three with
no producer as of this writing: `HenselLiftDescentHypotheses`, the
`toMonicLiftData` modP→lift transport, and `InitialLiftedFactorSubsetPartitionEvidence`.

## The Mathlib layer is not CI-built — establish a baseline first

CI builds only bench + conformance targets (`ci.yml`, `conformance.yml`);
it does **not** build `HexBerlekampZassenhausMathlib`. So that layer can be
**hard-red on main** — a real elaboration error, not just the known
`sorry`s — whenever an executable→Mathlib split is mid-flight (e.g. the
dilation remodel left `Basic.lean` failing at `:15990` while #6804/#6772 were
open), and merges keep flowing because nothing gates it.

Because nothing gates it, a green CI rollup does **not** mean a Mathlib-layer
file compiles — a reviewer of such a PR must build it locally to verify it at
all. A fresh worktree has no built Mathlib, so run `lake exe cache get` first
(fetches prebuilt oleans in minutes; a from-scratch Mathlib compile is hours).
Only the project's own files then rebuild.

Before attributing a Mathlib-layer build failure to your own change, build the
**unmodified** target on a clean tree to get a red/green baseline
(`lake build HexBerlekampZassenhausMathlib.<Module>`), and `git diff origin/main
-- <file>` to confirm the failing file is untouched by you. When you capture
that build with `| tee <log>`, the pipeline's exit status is `tee`'s, so a
`run_in_background` completion notification reports **exit 0 even on a failed
build** — judge red/green by grepping the log for `error:` / `build failed`,
never by the reported exit code. Grep only *after* the build has finished: a
still-running background build's log shows zero `error:` lines simply because
elaboration has not yet reached the broken file, so a premature grep reads
false-green. Wait for the `Built <target>` / process-exit signal (or an
`error: build failed` line) before concluding, and do not launch overlapping
`lake build`s to "confirm" — they serialize on the worktree lock and muddy
attribution. A faster
single-build attribution when your change is purely additive *within* the same
file: Lean reports every per-declaration error and keeps elaborating past a
failed declaration, so if the build log's only `error:` line numbers fall
**outside** the line range of your additions (a warning emitted *after* the
failing line but *before* your code confirms elaboration reached you), your
declarations compiled — no clean-tree rebuild needed. But that passive read
gives **no signal when the failing line is the highest line in the whole log**:
proof-only theorems emit no warning (only `sorry` does), so additions *below*
the pre-existing breakage produce no later diagnostic to confirm elaboration
even reached them. In that case add a temporary `#check @yourTheorem` probe
right after each addition and rebuild: if it prints the full type (an `info` at
that line), you have proved both that elaboration ran past the earlier errors
*and* that the theorem typechecks; if the name failed it errors "unknown
identifier" instead. Remove the probes before committing. This is the reliable
way to verify additive wrappers stranded in a file that is red from a separate
mid-flight migration (e.g. adding cap-bound wrappers to `Recovery.lean` while
its recovery-direction proofs are red from a partial monic-lift migration): the
full-module build never goes green, but the wrappers are still verifiably
correct, so land them and name the owning migration issue in the PR body. If
your target's
file (or a file it imports, like `Basic.lean`) is already red and your additions
*depend on* the broken declarations, they cannot be verified at all. Land the
parts that *do* build in isolation, and preserve the blocked parts (source in
the issue comment) for a follow-up gated on the remodel issue rather than
merging unverified Lean.

The inverse also bites: **fixing a red dependency unmasks pre-existing breakage
in files downstream of it.** If `Basic.lean` is red on main, every module that
imports it (`Recovery.lean`, `IntReductionMod.lean`, `PartitionRefinement.lean`)
is never reached by a full-target build — so a clean-`origin/main`
`lake build HexBerlekampZassenhausMathlib` is **not** a valid baseline for those
downstream files; it stops at `Basic.lean` and reports zero downstream errors
purely because elaboration never got there. When your PR makes `Basic.lean`
green, the full target proceeds and surfaces those downstream errors for the
first time — they look like regressions but are not. Confirm by grepping that
the failing downstream file uses none of the declarations your diff touched
(`grep -ln <changed-lemma-names> <downstream>.lean`) and that the error shapes
are internal to it (e.g. `unfold <unchanged-def>` failures, a kernel cascade on
some `…_ne_none_…` constant from a separate mid-flight migration). Then verify
your deliverable with the **module** build (`lake build
HexBerlekampZassenhausMathlib.Basic`), note the unmasked downstream breakage in
the PR body as pre-existing/out-of-scope (name the owning migration issue), and
do **not** try to fix it — that is a different issue's remodel.

## Pre-existing sorries

`HexBerlekampMathlib/Basic.lean` and `HexHenselMathlib/Correctness.lean` ship
`sorry`s (the `toMathlibPolynomial` coeff bridge etc.). Those warnings are not
from your file; building on them is the established project state. Only check
that *your added lines* are `sorry`/`axiom`/`native_decide`-free
(`git diff -U0 <file> | grep '^+' | grep -iE 'sorry|axiom|native_decide'`).

## Heartbeat timeouts in heavy assembly proofs

`maxHeartbeats` is a **per-declaration** budget, not per-tactic. In big proofs
over large terms (full Sylvester-of-products matrices, `degreeLT` reprs), a
`(deterministic) timeout at whnf`/`isDefEq`/`tactic execution` error names the
line where the *shared* budget hit zero — **not** the pathological tactic. Don't
restructure around the reported line first; it is usually a cheap `omega` or
`exact` that simply ran last.

- First remedy: `set_option maxHeartbeats 400000 in` on the declaration (the
  common Mathlib value; raise further only if needed). Once the budget is large
  enough, the *real* error often surfaces (e.g. an inline `by omega` whose
  target type wasn't yet determined because it sat under `lt_of_le_of_lt _ (by
  omega)` — fix by giving the bound an explicitly-typed `have h2 : … := by
  omega` so its goal is fully concrete before `omega` runs).
- Keep the capstone thin: factor heavy sub-steps (column-formula computations,
  `repr` evaluations) into their own lemmas. Each gets a fresh budget, and the
  capstone only pays for delegating.
- A `let`/`set`-bound abbreviation of a huge term in the *goal or context* makes
  `omega` and defeq checks whnf that term — avoid binding the matrix; write it
  out or `clear_value` only when the value is genuinely unneeded downstream.

## Verifying executable-layer changes: build the module, not the target

`lake build HexBerlekampZassenhaus` (the whole target) drags in
`CrossCheck` (~11 min, external oracle) and `Conformance` (~2 min) — it is a
~15-minute build, not a fast check. For iterating on a lemma, verify the
specific module (`lake build HexBerlekampZassenhaus.Basic`,
`lake build HexPolyZ.Basic`); that elaborates your declarations in seconds and
is the real correctness signal for theorem-only additions, which never affect
the `#guard`/oracle steps. Run the full target once at the end.

Do **not** launch a second `lake build` in the same worktree while one is still
running its tail jobs — they serialize on lake's per-worktree build lock, so the
second just blocks and looks "stuck". (This machine also runs concurrent builds
from *other* pod worktrees; `pgrep lake` showing many processes is normal and
not your build.)
