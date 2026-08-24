# HexPolyFpMathlib phases 1 through 5 recorded

## Accomplished

Rebased `poly-fp-mathlib-phases-1-5` onto `origin/main` (picking up #9366's
correspondence-only Phase 3/4 subsections and #9367's SPEC comparator
rewording) with no conflicts, then recorded
`libraries.yml[HexPolyFpMathlib].done_through` 0 -> 5 in six commits: the
Phase 1 bump, the reviewer's token commit, then one commit per remaining phase,
each carrying that phase's evidence in its message.

### Granularity convention

Not strictly one-phase-per-PR. Most bumps in history move one step
(`b8ffdbf6e`, `cb7c8137b`, `2e95578a4`, `e4653d540`, `cf69e6d6e`), but a
library catching up after a refactor or a late classification records several
phases at once: `cf8890930` (HexMvPoly/HexMvPolyMathlib 0 -> 4), `3bfcafa20`
(HexRCF 0 -> 3), `617acbffb` (HexRealRootsMathlib 1 -> 3), `5399b8e90`
(HexResultant 1 -> 4 and HexResultantMathlib 1 -> 3), `346cca9a1`
(HexMvPoly 4 -> 6). This library is exactly that shape: `15a68c4ac` extracted
it from HexBerlekampMathlib and seeded it at 0. Splitting the commits keeps
the per-phase evidence readable and leaves the PR split open.

The Phase 1 bump precedes the token commit, because `PLAN/Phase2.md` gates the
start of Phase 2 on `done_through >= 1`.

### Per-phase evidence

**Phase 1.** Deps HexPolyFp, HexPolyMathlib, HexModArithMathlib are all at
`done_through: 7`, past the `>= 1` gate. `lake build HexPolyFpMathlib` green,
1656 jobs, 67s. The SPEC-promised surface is all present in
`HexPolyFpMathlib/Basic.lean` with nothing deferred. Data-level declarations,
in full: `fpPolyToPolynomial` (`:43`, a `Finset.sum` of monomials),
`polynomialToFpPoly` (`:48`, `DensePoly.ofList` over `List.range (natDegree +
1)`), `fpPolyEquiv` (`:164`), `toMathlibPolynomial` (`:219`), and the
`commRing` instance (`:385`), whose `sub` and `neg` fields carry the executable
`DensePoly` operations. Each computes what its name says.

**Phase 2.** `status/hex-poly-fp-mathlib.scaffolding-reviewed` is the
attestation, committed by a reviewer agent other than the scaffolding author.
Two corrections were made to it while recording the phase: its data-level
enumeration was short by `toMathlibPolynomial` and `commRing`, and it described
#9367 as open. The three gaps it identified are filed:
https://github.com/kim-em/hex-dev/issues/9370,
https://github.com/kim-em/hex-dev/issues/9371,
https://github.com/kim-em/hex-dev/issues/9372. All three are additive surface
or hygiene, so none blocks the token.

**Phase 3**, under `PLAN/Phase3.md` §"Correspondence-only mathlib layers".
`conformance/HexPolyFpMathlib/` does not exist and never has (`git log --all`
on that path is empty); the `HexConformance` globs and
`scripts/conformance_targets.py` do not name it. The layer carried no checks:
`15a68c4ac` touched no path under `conformance/`, and HexBerlekampMathlib has
no conformance module either.

Per-operation coverage in the owners, and the two gaps the audit found:

- The dense ring surface — add, sub, mul, derivative, `C`, `monomial`, `X` —
  is hex-poly's, because `FpPoly p` is
  `abbrev FpPoly (p : Nat) [ZMod64.Bounds p] := DensePoly (ZMod64 p)`
  (`HexPolyFp/Field.lean:848`) and the transport lemmas are stated about
  `Hex.DensePoly.*`. Covered in `conformance/HexPoly/Conformance.lean` at
  `:167-169`, `:171-173`, `:213-220`, `:222-227`, `:229-235`, `:251-257`, with
  accessors at `:183-185` and `:187-189`.
- `dvd` is proved from a multiplication witness and `toMathlibPolynomial_mul`
  (`Basic.lean:352-355`), so its executable content is multiplication —
  including the oracle-backed FpPoly-level `mul` cases in
  `conformance/HexPolyFp/EmitFixtures.lean` at p in {5, 11, 31}, checked
  against python-flint `nmod_poly` by `scripts/oracle/polyfp_flint.py:137-147`.
  Not gcd or divrem, which the operation never reaches.
- `neg` and `linearPow` had no owner-side check anywhere. Both are now covered
  by new `#guard`s in `conformance/HexPolyFp/Conformance.lean`, with the
  module docstring's three lists extended to match the per-library module
  contract in `SPEC/testing.md`. `lake build HexPolyFp.Conformance` green, 99
  jobs, 0.6s; flipping one expected coefficient makes it fail.
- The Frobenius, modular-composition and square-free surface was already
  guarded at p = 5 in the same module, with oracle-backed `frobenius`,
  `gcd`, `divrem` and (at p = 5 only) `squarefree` emissions alongside.

**Phase 4**, under `PLAN/Phase4.md` §"Correspondence-only mathlib layers". Zero
advertised operations in either track: no `Bench.lean`, no `Bench/`, no
`lean_exe` bench entry, no `proof_probes` root, no elaborator or tactic. No
`phase4` block, no headline report required.

The SPEC's comparator declaration needed a fix. #9367 landed the right reason
string, `correspondence-only-layer`, but named hex-poly-fp as the sole
computational performance owner, which the code does not support: the dense
ring surface belongs to hex-poly. The declaration now names both owners and
maps the operation families to them, and says plainly that `linearPow` has no
bench target in either — it is a structural recursion for kernel reduction
whose only call sites are theorems, so a dedicated target would be a false
attribution.

**Phase 5.** Zero sorries: `grep -rn sorry HexPolyFpMathlib/
HexPolyFpMathlib.lean` exits 1, as does the same grep for `sorryAx` and
`axiom`. `lake build HexPolyFpMathlib HexBerlekampMathlib HexGF2Mathlib
HexGFqMathlib` green, 2333 jobs, 311s (the host was heavily loaded; the
absolute number is not a performance datum).

### Checkers

`python3 scripts/check_dag.py` exits 0. `python3 scripts/check_phase4.py`
reports `Phase 4 checks passed`. `python3 scripts/status.py` moves
HexPolyFpMathlib to Phase 6 and unblocks HexBerlekampMathlib's Phase 4 gate on
this library.

### libraries.yml comment

Replaced the paragraph explaining why the counter sat at 0 with a shorter note:
the extraction origin, the Phase 2 token, and the correspondence-only
classification behind the absent conformance module, bench target and `phase4`
block.

## Current frontier

HexPolyFpMathlib is at `done_through: 5`. HexBerlekampMathlib's Phase 4 gate on
it is satisfied; it now waits only on HexBerlekamp reaching 4.

## Next step

Phase 6 (proof polishing) for HexPolyFpMathlib, or issues 9370 / 9371 / 9372,
whose fixes are Phase-1-shaped additive surface and would be cheaper to land
before a Phase 6 audit reads the same file.

## Blockers

None. One observation worth passing on rather than acting on: hex-poly's
conformance module does not advertise `neg` in its covered-operations list,
and hex-poly's own `#guard`s do not exercise it. The gap is closed here at
`ZMod64 5`, which is the instantiation this layer transports, but the generic
`DensePoly R` case remains unchecked in its own owner.
