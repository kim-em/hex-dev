# Phase 3: Conformance Testing

**Coupling:** dep-coupled. Library L can start Phase 3 once
`libraries.yml[L].done_through ≥ 2` and every `d ∈ L.deps` has
`libraries.yml[d].done_through ≥ 3`.

Conformance testing comes **before** proofs. No point proving theorems
about wrong implementations.

Phase 3 follows `SPEC/testing.md`. Read that file before dispatching
or picking up a Phase 3 issue — it defines the per-library module
contract, the banned anti-patterns, the preferred idioms
(`#guard_msgs in #eval`, `#guard`), and the CI mandate.

The three profiles are `core` / `ci` / `local`; the three execution
modes are `always` / `if_available` / `required`. The `core` profile
is `always` and runs on every push and PR.

## Exit criteria

Phase 3 is done for a library `HexFoo` when all of:

1. `conformance/HexFoo/Conformance.lean` exists and satisfies the **per-library
   module contract** in
   [SPEC/testing.md](../SPEC/testing.md#per-library-module-contract).
   In particular:
   - opens with a docstring declaring oracle / mode / covered
     operations / covered properties / covered edge cases for this
     library;
   - has ≥1 elaboration-time check per advertised public operation;
   - has ≥1 property `#guard` per advertised algebraic property;
   - has ≥3 cases per operation (typical / edge / adversarial);
   - contains no banned anti-patterns (dead expected fields,
     single-case coverage, serialise-roundtrip-to-literal, metadata
     with no consumer, `native_decide`).

2. `conformance/HexFoo/Conformance.lean` is listed in the
   `HexConformance` globs in `lakefile.lean`, so `lake build
   HexConformance` elaborates every check without placing test code in
   the public `HexFoo` umbrella.

3. The conformance/oracle tail of `.github/workflows/ci.yml` is green
   on the PR that lands the module, and remains green on
   `main`. If the library's oracle mode is `always` or `required`,
   the oracle-backed check is wired in the same PR; if
   `if_available`, wiring the oracle is a follow-up.

4. Record completion by bumping `libraries.yml[L].done_through` to
   `3` in the same PR.

Reviewer checklist for Phase 3 PRs:

- [ ] Module docstring declares oracle, mode, covered operations,
  covered properties, covered edge cases.
- [ ] Every public operation listed in the library's SPEC file has
  ≥1 elaboration-time check.
- [ ] Input sizes pushed toward the upper end of SPEC/testing.md
  § "Profile sizes" ranges (or a comment explains why a smaller size
  was chosen).
- [ ] Every property named in the module docstring has ≥1 `#guard`.
- [ ] Every edge case named in the module docstring has ≥1 fixture.
- [ ] No `expected*` struct field is unreferenced.
- [ ] No `#guard` / `example` where RHS is a literal copy of the
  LHS's evaluation (i.e. the assertion carries content beyond "the
  evaluator is deterministic").
- [ ] No `#guard f(x) = literal` where the literal was obtained by
  running `f`. Each `#guard`'s expected value must be independently
  derivable from the function's documented contract.
- [ ] `lake build HexFoo HexConformance` green.
- [ ] Conformance/oracle tail green on the PR.
- [ ] `HexConformance` globs build this library's module; no CI matrix
  is introduced.
- [ ] Every `emitResult` in `HexFoo/EmitFixtures.lean` is
  cross-checked by the corresponding oracle script under the three
  rules in
  [../SPEC/testing.md §Oracle discipline](../SPEC/testing.md#oracle-discipline):
  independent expected value (no re-running the operation under
  test on Lean's output), uniform contract across input classes (no
  shape-dependent bypass to a weaker invariant), and a tracking
  issue for any deliberately uncovered op (with the conformance
  docstring not claiming it as covered).

### Correspondence-only mathlib layers

The criteria and checklist above presuppose an executable surface to
conform to. A library explicitly classified by `mathlib: true` and
`correspondence_only: true` whose API is correspondence statements alone,
with no executable reifier, certificate checker, or tactic of its own, has no
conformance module at all:
`conformance/HexFooMathlib/Conformance.lean` must not exist, per
[SPEC/testing.md §Banned anti-patterns](../SPEC/testing.md#banned-anti-patterns).
For such a library Phase 3 is done when all of:

1. `libraries.yml[L].correspondence_only` is `true`,
   `conformance/HexFooMathlib/Conformance.lean` is absent, and no
   `HexConformance` glob in `lakefile.lean` names it.
   `scripts/conformance_targets.py` discovers targets by that
   filename, so the library is absent from the conformance CI list.

2. The library SPEC declares `correspondence-only-layer`, identifies the
   computational owners on `Computational conformance owner(s):` and
   `Computational performance owner(s):` lines, and the PR audits
   whatever checks the layer carried and cites, for each
   operation the layer transports, the coverage that lives in the
   named computational owner or owners (more than one owner is normal,
   since a layer may transport operations from several Mathlib-free
   libraries). A check that exercises only the layer's own conversion
   or index helpers has no executable destination to migrate to and is
   deleted rather than moved; it is ceremonial, not coverage.

3. `lake build HexFooMathlib` is green on the PR and remains green on
   `main`.

4. Record completion by bumping `libraries.yml[L].done_through` to
   `3` in the same PR.

A Mathlib-importing library that owns an executable reifier,
certificate checker, or tactic is not correspondence-only. It takes the
ordinary criteria, with its library SPEC defining that runtime contract
and its CI reachability.

## Oracle wiring (forward reference)

Default oracle assignments live in
[SPEC/testing.md § Oracle strategy](../SPEC/testing.md#oracle-strategy).
Individual `conformance/HexFoo/Conformance.lean` modules name the specific
oracle chosen in the module docstring.

Implementation details for `ci` and `local` profiles — JSON/JSONL
case format, driver script shape, Nix-Sage wiring — are specified
by the first library to need them, not upfront.
