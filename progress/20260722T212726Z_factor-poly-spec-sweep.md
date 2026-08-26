# factor_poly / irreducibility: top-level SPEC sweep

## Accomplished

- Audited the top-level `SPEC/` tree against the four per-library SPEC
  sections for the `factor_poly` / `irreducibility` tactic family
  (hex-berlekamp, hex-berlekamp-zassenhaus, and the two Mathlib bridges).
- `SPEC/SPEC.md`: added a "user surface" paragraph to *What we're
  building* (elaborator forms, provider architecture, trust model,
  coverage boundary) and pointed the `GF(2^128)` application at the
  `irreducibility` tactic.
- `SPEC/Libraries/README.md`: the four one-line summaries and the four
  linked-list entries now name the tactic drivers / providers.
- `SPEC/Libraries/hex-rcf.md`, `SPEC/Libraries/hex-real-roots-mathlib.md`:
  retargeted the two references to the deleted `irreducible_cert` tactic
  at the `factor_poly` / `irreducibility` compiled-prep / kernel-verify
  pattern.
- `SPEC/testing.md` does not catalog per-suite test files, so
  `FactorTacticTests` / `FactorPolyTests` are intentionally not listed
  there; `SPEC/future-work.md` had no irreducibility-tactic entry to
  retire.

## Current frontier

Docs-only sweep; PR against `factor-poly/eisenstein` at the end of the
stacked series.

## Next step

None for this corner once the PR merges with the stack.

## Blockers

None.
