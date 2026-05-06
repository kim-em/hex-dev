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

1. `HexFoo/Conformance.lean` exists and satisfies the **per-library
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

2. `HexFoo/Conformance.lean` is imported from `HexFoo.lean`, so
   `lake build HexFoo` elaborates every check.

3. The conformance CI job at `.github/workflows/conformance.yml` is
   green on the PR that lands the module, and remains green on
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
- [ ] `lake build HexFoo` green.
- [ ] Conformance workflow green on the PR.
- [ ] CI conformance matrix builds this library (either via the
  derivation script picking up the root-import, or via an explicit
  matrix entry).
- [ ] Every `emitResult` in `HexFoo/EmitFixtures.lean` is
  cross-checked by the corresponding oracle script under the three
  rules in
  [../SPEC/testing.md §Oracle discipline](../SPEC/testing.md#oracle-discipline):
  independent expected value (no re-running the operation under
  test on Lean's output), uniform contract across input classes (no
  shape-dependent bypass to a weaker invariant), and a tracking
  issue for any deliberately uncovered op (with the conformance
  docstring not claiming it as covered).

## Oracle wiring (forward reference)

Default oracle assignments live in
[SPEC/testing.md § Oracle strategy](../SPEC/testing.md#oracle-strategy).
Individual `HexFoo/Conformance.lean` modules name the specific
oracle chosen in the module docstring.

Implementation details for `ci` and `local` profiles — JSON/JSONL
case format, driver script shape, Nix-Sage wiring — are specified
by the first library to need them, not upfront.
