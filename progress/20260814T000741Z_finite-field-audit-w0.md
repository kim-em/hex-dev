# Finite-field libraries: audit, and workstream 0

Audit of `hex-gf2`, `hex-gf2-mathlib`, `hex-gfq-field`, `hex-conway`,
`hex-gfq`, `hex-gfq-mathlib` (plus `hex-gfq-ring` where it could not be
separated from `hex-gfq-field`), and the first slice of the resulting
work.

## Accomplished

Audited all seven libraries against their SPECs, `PLAN/Phase1.md` through
`PLAN/Phase7.md`, and the manual. Six of the seven read `done_through: 7`
and the set contains no `sorry`, `axiom`, or `native_decide`; the audit
found five independent ways the recorded state overstates completion.
No unsoundness: an uncommitted `(p, n)` is unconstructible at the type
level at all three entry points, with no junk value or `Inhabited`
fallback anywhere.

Landed in this change (workstream 0, the accuracy and coverage slice):

- **The CI change was dropped.** It began as a claim that neither
  `HexGF2Mathlib` nor `HexGFqMathlib` was built by the required check. That was
  wrong: `ci.yml` builds `HexManual`, whose `HexGFq` chapter imports
  `HexGFqMathlib`, which imports `HexGF2Mathlib`. Restated as a caching
  improvement, it was wrong a second time: `ci.yml` already appends `HexManual`
  when collecting the outputs to publish, so both libraries' oleans are already
  in the mapping. Nothing was left to justify, so the edit is gone.

- **Two factual errors in the manual corrected.**
  `Chapters/HexGF2.lean` claimed the `GF(2ⁿ)` Mathlib correspondence was
  supplied by companions of downstream libraries "not by this library";
  `HexGF2Mathlib` is exactly that companion and is now named.
  `Chapters/HexConway.lean` claimed Tier 2 and Tier 3 "live in separate
  libraries above this one"; they belong to `hex-conway` per its SPEC and
  do not exist. The replacement states what Lean actually checks about a
  committed entry (monic, irreducible, right degree) and what it does
  not (that the entry is the *Conway* polynomial for its pair).
- **Stale headers refreshed.** `bench/HexGFq/Bench.lean`,
  `conformance/HexGFq/CrossCheck.lean`,
  `conformance/HexGFq/EmitFixtures.lean`, `bench/HexConway/Bench.lean`,
  `HexGFq.lean`, and `HexConway.lean` all still described a one-entry
  Conway table. There are 36 committed generic entries and 6 packed ones.
  The bench header now says plainly that its degree-one pinning is
  outstanding work rather than a limit of the public API.
- **`HexGF2` simp set made confluent.**
  `isZero_eq_true_iff_words_eq_empty` and `isZero_iff_eq_zero` were both
  `@[simp, grind =]` on the identical left-hand side `p.isZero = true`,
  so the normal form depended on rule order. The propositional form wins;
  the representation-level form keeps its statement and loses the
  `simp` attribute, but keep their `grind` triggers: `grind =` registers an
  E-matching theorem rather than an oriented rewrite, so two triggers on one
  term let congruence closure learn both consequences instead of racing.
  Dropping them cost `grind` the step from `isZero = false` to
  `words ≠ #[]`, which a probe confirmed. Added `isZero_eq_false_iff_ne_zero`
  so the failing branch normalises to `p ≠ 0`, and `words_eq_empty_iff` so a
  goal stated about `words` reaches the same normal form as one stated about
  `isZero`. Dropped `@[simp]` from `degree_eq_of_degree?_eq_some`, whose
  left-hand side `p.degree` does not determine `d`; all sixteen call sites
  already apply it explicitly.

## Current frontier

Workstream 0 of the plan is complete and verified. The remaining
workstreams are scoped but not started:

1. `hex-conway` Tier 1 depth then Tier 2. The
   `rebuild_luebeckConwayPolynomial?` command the SPEC specifies does not
   exist, so the table and its 36 hand-written Rabin certificates are
   maintained by hand, which is why it has stalled at 36 of the 186
   entries already cached in `scripts/oracle/luebeck_conway_cache.json`.
   `HexConway/Certificates.lean` carries 35 `maxHeartbeats` bumps (31 at
   8M, 4 at 20M); `HexConway.Certificates` takes 27s to elaborate. The
   SPEC's "as much of the table as possible subject to a few minutes"
   budget has never been measured. Tier 2 then delivers
   `conwayPoly_compat` and the subfield embeddings, which is the whole
   point of choosing Conway polynomials and is currently undelivered.
2. `hex-gf2-mathlib` uses a project-local `RingEquiv` (`Basic.lean:54`)
   that shadows `≃+*`, the only library in the repo that does. Mathlib's
   `RingEquiv` has the identical typeclass context, so nothing is being
   avoided, and no Mathlib theorem transports along the local structure.
   Then `hex-poly-fp-mathlib` as a new home for
   `FpPoly p ≃+* Polynomial (ZMod p)`, currently owned by
   `HexBerlekampMathlib` at `done_through: 3`.
3. `hex-gf2` has no `Lean.Grind` instances at all, though every component
   law is proved; `HexGFqField` bundles its equivalents.
4. The CLMUL intrinsic paths are never compiled: `lakefile.lean:24` omits
   `-mpclmul`, so x86-64 builds take the portable branch and only Apple
   silicon compiles `vmull_p64`. Each machine tests one path, neither
   tests the other, and the SPEC requires both.
5. Phase 7 is recorded complete for `hex-gf2` and `hex-gfq` without their
   anchored tutorials, of which `HexManual/Tutorials/` has one of four.

## Next step

Workstream 1a: the `rebuild_luebeckConwayPolynomial?` command. It gates
1b (measure the budget, grow the table), which in turn should land before
Tier 2 so the compatibility checkers are written once against the final
table size.

Workstreams 2 and 3 are independent of 1 and of each other, so they can
run in parallel. Workstream 2b is the only piece with blast radius
outside these libraries and wants its own branch.

## Blockers

None for the plan as scoped. Two things worth flagging:

- The Kummer-Dedekind tutorial is anchored to `hex-gfq` in
  `PLAN/Phase7.md:110`, but `SPEC/tutorials.md:106-112` names
  `hex-poly-z` and `hex-berlekamp-zassenhaus` as its primary libraries
  and does not mention `hex-gfq`. `HexBerlekampZassenhaus` is at
  `done_through: 0`, so the tutorial is blocked regardless of anchor. The
  plan re-anchors it.
- `lake build HexManual` should be part of the verification for any change
  touching a library the manual documents. Leaving it out of the Conway branch's
  checks let a stale `#guard` reach CI.
- `lake build HexManual` failed once in
  `HexBerlekampZassenhausMathlib/SquareClass.lean` when run concurrently
  with another `lake` invocation on the same worktree, and passed on a
  clean re-run. The module builds standalone, has no dependency path to
  anything changed here, and CI plus Pages are green on the base commit.
  Recorded in case the same transient shows up again; concurrent `lake`
  invocations against one worktree look like the cause.

## Verification

```
lake build HexGF2 HexGF2Mathlib HexGFqMathlib HexConformance \
  HexManual hexconway_bench hexgfq_bench          # 9914 jobs, clean
python3 scripts/check_dag.py                     # OK
python3 scripts/check_phase4.py                  # OK
python3 scripts/check_file_line_counts.py        # OK
python3 scripts/check_copyright_headers.py       # OK
git diff --check                                 # clean
```

The conformance build elaborates every `#guard`, so it exercises the
changed simp set rather than only typechecking it.
