# HexBerlekamp: Phases 5, 6, 7

## Accomplished

`libraries.yml[HexBerlekamp].done_through` advanced 4 -> 7 in three
commits on `berlekamp-phases-5-7`, one per phase.

**Phase 5** (`chore(berlekamp): record Phase 5 completion`). Verification
only, no source change. Zero `sorry`/`axiom`/`native_decide` across the
19 modules; `lake build HexBerlekamp` green on
`leanprover/lean4:v4.34.0-rc2`; `HexBerlekamp.Conformance` and
`HexBerlekamp.FactorTacticTests` elaborate their `#guard`s; no open
bench-found or conformance-found issue targets the library (the only open
issue matching `HexBerlekamp` is #9425, a `check_dag.py` tooling issue).

**Phase 6** (`polish(berlekamp): complete Phase 6`). The Mathlib linter
audit ran from a throwaway file *outside* the library (the library is
Mathlib-free, so it cannot carry a `LintTests` module the way `HexRCF`
does) importing `HexBerlekamp` plus Batteries' linter framework and
running `#lint- docBlame docBlameThm' in HexBerlekamp`. 22 hits at the
start, 0 at the end:

- 5 `docBlame` + 1 `docBlameThm'` -> docstrings.
- 3 `simpNF` -> `@[simp]` dropped from `degreeBucketProduct_singleton`,
  `primeFieldLinearProduct_factor_count`, and `Packed.toNat_toZMod`, with
  the reason recorded in each docstring. Names kept.
- 13 `unusedArguments` -> 14 dead `[ZMod64.PrimeModulus p]` binders and
  the unused `[ZMod64.Bounds p]` of `Packed.modWord` removed. `Bounds` is
  a `Prop` class, so `modWord` compiles identically. Removing the binders
  cascaded: each round exposed the next lemma whose binder had only been
  kept alive by a now-deleted user, so the sweep iterated to a fixpoint.

Also: docstrings for every public declaration in the umbrella (the gap
was `PackedKernel`, one `Factor` lemma, and the `@[csimp]` bridge in
`DelayedKernel`); two genuinely dead private helpers removed; five
verbatim copies of `1 != 0 in ZMod64 p` and two copies of the
`factorProduct` cons/append laws collapsed onto the public upstream names;
and all 97 Lean-4.34 `if_pos`/`dif_neg`/... deprecation warnings renamed
to the `ite_eq_*`/`dite_eq_*` aliases, leaving a warning-free build.

A stale `RabinShape` docstring describing the soundness proof as
delegating to "foundational sorries" was corrected; the library has none.

**Phase 7** (`doc(berlekamp): complete Phase 7`). The chapter and the
anchored `AESModulus` tutorial already satisfied `check_phase7.py` and
`check_manual_split.py` with the counter at 7. The real gap was
`HexBerlekamp/README.md`, which had the five required headings but a
two-line quickstart. Rewritten to the `SPEC/readme.md` shape, with a
20-line quickstart build-checked as a temporary module in
`HexReleaseTests` and two headline theorem signatures quoted verbatim.

## Current frontier

All checkers pass: `check_dag`, `check_phase4`, `check_phase7`,
`check_file_line_counts`, `check_copyright_headers`,
`check_manual_split`, `check_released_manifest`, `check_trust_surface`,
`check_factor_sweep_freshness`. Green builds: `HexBerlekamp`,
`HexBerlekamp.Conformance`, `HexReleaseTests`, `HexConway`,
`HexGFqField`, `HexBerlekampMathlib`, `HexBerlekampZassenhaus`,
`HexManual`. `hexberlekamp_bench verify` reproduces all 26 Lean
registrations.

13 blob-transition entries were appended to
`scripts/bench/proof_only_runtime_exemptions.json` (12 `.lean` files, one
of them refreshed after a later docstring fix) against the recorded
`hex-factor` measurement commit `7425e083`. No executable factorization
code changed.

## Next step

The branch is unpushed and has no PR. `origin/main` advanced by four
commits while this ran, so a rebase is needed before opening one.

The same Lean-4.34 `if_pos`/`dif_neg` deprecation wave is still live in
other libraries (`HexMatrix/ElementaryAlgebra.lean`, `HexPolyFp/Compose.lean`,
`HexConway/Api.lean`, `HexGF2Mathlib/Basic.lean`,
`HexNumberFieldMathlib/Lazy.lean`, ...). The rename is mechanical and
warning-only; it belongs with each library's own Phase 6 rather than in
this one.

## Blockers

None.
