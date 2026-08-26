# Issue #8566: irreducible_cert tactic (Part 2 of #8552)

## Accomplished

All of deliverables 1-3 on branch `issue-8566` (rebased onto main after
Part 1 PR #8565 merged mid-session):

1. `9d0b557e` — kernel-reducible integer checker. `checkCertAtFactorLinear` /
   `checkFactorCertsLinear` / `checkForPolynomialLinear` /
   `checkIrreducibleCertLinear` (`HexBerlekampZassenhaus/Basic.lean`) replay
   nested Rabin certificates through
   `Berlekamp.checkIrreducibilityCertificateLinearIncremental` (O(n·p) kernel
   work per factor). Implication chain back to the committed checker:
   `checkIrreducibilityCertificate_of_linearIncremental`
   (`HexBerlekamp/Irreducibility.lean`, from
   `checkPowChainLinearIncremental_spec`) and `checkIrreducibleCert_of_linear`
   (per-prime `Hex.Nat.Prime` hypothesis), so `checkIrreducibleCert_sound` is
   consumed unchanged.
2. `a273f783` — Mathlib wrappers (`HexBerlekampZassenhausMathlib/Basic.lean`):
   `checkIrreducibleCertLinear_sound` (∀-form primality) and
   `irreducible_of_checkIrreducibleCertLinear` with all four hypotheses as
   `Bool = true` slots — the tactic fills each with `Eq.refl true` and the
   kernel does all verification by reduction.
3. `811bc880` — `CertReify.lean` (pure `HexX → Expr` reifier via public
   constructors: `ZMod64.ofNat`, `FpPoly.ofCoeffs`, `boundsOfDecide` for
   instance fields; canonical serializations for comparison),
   `IrreducibleCert.lean` (the tactic: unsafe-eval of `certifyIrreducible?`,
   reify, emit; opaque/implemented_by eval helpers), and
   `IrreducibleCertTest.lean` (round-trip tests reify→check→eval-back→compare;
   end-to-end examples on the four Part 1 guard polynomials; axiom cone pinned
   to `[propext, Classical.choice, Quot.sound]` via `#guard_msgs`; clean
   failure message pinned on a reducible input).
4. `1961485f` — conformance `#guard`s for `checkIrreducibleCertLinear`
   round-trips (compiled form of the kernel replay).

## Key findings

- Array.all / Array.foldl / `decide (Nat.Prime p)` (Mathlib's
  `Nat.decidablePrime`) all kernel-reduce on this toolchain — spiked before
  building (`/tmp/kernel_spike.lean` pattern, `decide +kernel`).
- `lake env lean` scratch files can NOT run the tactic (no `--load-dynlib` for
  the `Hex.ZMod64.mul` extern); tactic examples must live in lake-built
  modules. Editor sessions and CI are fine.
- `of_decide_eq_true h` with an expected *defined* Prop (e.g. `Primitive f`)
  makes the elaborator synthesize `Decidable` for the defined form; bind the
  underlying equation with `have` first.
- Incremental (not plain Linear) pow-chain replay chosen analytically:
  O(n·p) vs O(Σ p^k); the empirical Linear-vs-Incremental comparison is
  deferred to the deliverable-4 sweep.

## Current frontier / Next step

Deliverable 4 (kernel_factor_sweep.py certifying series) depends on the
unmerged `kernel-decide-series` branch (2 commits: the sweep harness +
frontier record). Per the issue's own dependency note, scoped as a follow-up
commit on that branch — file a follow-up issue at PR time.

Second opinion (Codex): no soundness or checker-correctness issues found;
addressed its two actionable findings (exception-catching Except-based
evalExpr wrappers with the underlying evaluator message surfaced in the
tactic error, and a real diagnostic on the final defeq mismatch instead of
"internal error"). Kept IrreducibleCertTest in the umbrella deliberately:
that is what makes the end-to-end tests CI-gated; this repo has no separate
test target for Mathlib layers.

Remaining: open PR closing #8566, follow-up issue for deliverable 4.

## Blockers

None.
