# 2026-07-02 — issue #8521: precision cap vs bhksBound core

Session type: feature (interactive worktree session, branch `issue-8521`).

## Accomplished

- Answered the issue's question 1: `bhksBound core ≤ factorFastPrecisionCap f`
  is **false**. Counterexample family `f = (xᵃ−1)(xᵃ⁺¹−1)`: `coeffNormSq f = 4`
  while the square-free core `f/(x−1)` has `coeffNormSq = 2a`, overtaking the
  degree-drop-of-1 penalty in `bhksBound` from `a = 18` (exact integer check;
  at `a = 18` the core's bound is ≈4.5× the old cap). So this was a genuine
  executable soundness gap, per the issue's option 2.
- Executable fix (`HexBerlekampZassenhaus/Basic.lean`): `factorFastPrecisionCap`
  now takes `max (bhksBound (normalizeForFactor f).squareFreeCore)
  (defaultFactorCoeffBound f)`. Removed the now-false-premised
  `bhksBound_le_factorFastPrecisionCap`; added
  `bhksBound_squareFreeCore_le_factorFastPrecisionCap`,
  `two_mul_bhksBound_squareFreeCore_lt_pow_cap`, and the
  `…_of_choosePrimeData` variant whose conclusion is exactly the `hprec` side
  goal at `LatticeTier.lean:456` on PR #8517's branch (`issue-8417`), with
  `hchoose` the hypothesis already in scope there. Pinned the counterexample as
  a `#guard`. Updated the SPEC's two formula-bearing paragraphs.
- Verification: full `lake build` green (4078 jobs, all `#guard`s);
  `HexBerlekampZassenhausMathlib` (merge-gating) green; fresh
  `hexbz_emit_fixtures` emission byte-identical to the committed fixture
  (200 lines); `bz_trace_gate.py` 50/0; `hexbz_bench verify` 18/18. No new
  `sorry`/`axiom`/`native_decide`.

## Current frontier

Second opinion (Codex) in flight; PR to open after addressing any concerns.
The lattice-tier `hprec` sorry itself lives on the open PR #8517 (branch
`issue-8417`), not on main — on main the whole lattice-branch lemma is one
sorry (#8417 scope). After this PR merges, that branch discharges its
line-456 sorry with
`Hex.two_mul_bhksBound_squareFreeCore_lt_pow_cap_of_choosePrimeData f
primeData hchoose`.

## Next step

Open PR closing #8521; comment on #8517 pointing at the one-liner discharge.

## Blockers

None.
