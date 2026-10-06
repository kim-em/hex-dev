## Verdict

| Library | Phase 2 | Phase 3 |
|---|---|---|
| **HexSignDet** | **Ready.** Commit the token and set `done_through: 2`. | **Justified once one documentation item (G1) is fixed.** No new tests are needed. |
| **HexSignDetTheory** | **Ready once one stale SPEC paragraph (G2) is rewritten.** The code is fine; the SPEC text is wrong. | **Not yet.** It needs HexSignDet at `done_through ≥ 3` first. G3 also affects what "`lake build HexSignDetTheory` green" actually attests. |

All other dependencies already meet the Phase-3 coupling rule. HexSignDet's are HexSturm 3, HexPoly 7, HexMatrix 7, HexRowReduce 7 and HexRank 4. The companion's are HexSturmTheory 3, HexPolyTheory 7, HexMatrixTheory 7 and HexRankTheory 4.

I couldn't run `git diff` against the merge base (shell permission was denied), so I reviewed the tree as it stands. I built nothing; build, kernel and CI status is taken from your description.

## Actionable gaps

**G1. HexSignDet conformance docstring doesn't follow the required contract (Phase-3 exit criterion 1).**
- `conformance/HexSignDet/Conformance.lean:43-53` is a prose paragraph.
- It lacks the `Oracle:` / `Mode:` / `Covered operations:` / `Covered properties:` / `Covered edge cases:` structure required by `SPEC/testing.md:49-67`. Compare `conformance/HexSturm/Conformance.lean:21-36`.
- Everything else for Phase 3 is in place:
  - the module is in the `HexConformance` globs (`lakefile.lean:1258`), along with `DescriptorCodec`;
  - six oracle tuples are wired in `scripts/ci/run_oracles.sh:65-74` (FLINT, field signs, common fields, two Z3 suites, JSON bytes);
  - `hexsigndet_field_checks` runs in CI;
  - `mapNodes` and the descriptor codec have checks (`Conformance.lean:1406-1419`, `DescriptorCodec.lean`).
- Write the structured docstring in the PR that sets `done_through: 3`, listing the external oracles with their modes.

**G2. The companion SPEC describes the wrong re-encoding algorithm.**
- `HexSignDetTheory/SPEC/hex-sign-det-theory.md:341-349` says to use "the source head P on its interval with queries for … H, all derivatives of H and target endpoint polynomials", then check that the target head's sign is zero.
- The code does the reverse. `HexSignDet/Reencode.lean:73-95` prepares the **target** domain `(head, a, b)` and queries the target's full derivatives followed by `source.raw.constraints` (old head, selected derivatives, strict old-endpoint polynomials). It then filters on `constraintSigns`.
- That is what `HexSignDet/README.md:415` and `ThomReencoding.lean` prove, and the proof is sound.
- Since the Phase-2 token attests against this SPEC, rewrite that paragraph to describe the target-domain algorithm before committing it.

**G3. The companion's headline theorems are outside its own library target.**
- All 18 modules in `adapters/HexSignDetTheory/` are built only by `HexQuerySemantics` (`lakefile.lean:705-718`). That includes `determine_correct`, `buildRoots_roots`, `compare_*`, `buildReencoding_isSome` and the new `Naturality` corollaries.
- The `HexSignDetTheory.lean` umbrella imports none of them.
- Their only outside imports are `HexSturmTheory.Soundness` and Tau Ceti `Thom`/`AbstractRolle`. Both are within declared dependencies, and `HexSignDetTheory/Foundation.lean:13` already imports Tau Ceti.
- The stated reason for the split is out of date: `HexSignDet/README.md:151` says `check_rootSum` is "in the development adapter", but it lives in `HexRealRootsTheory/TarskiSoundness.lean:24`.
- Nothing is unverified today, because CI builds `HexQuerySemantics`. But the Mathlib-library Phase-3 criterion ("`lake build HexSignDetTheory` green") would not touch the headline API. A future release split copying `HexSignDetTheory/` would also leave it behind.
- Either move or glob these modules into the `HexSignDetTheory` lean_lib, or have the Phase-3 record name `HexQuerySemantics` explicitly. I recommend moving them.

**G4. Minor stale text, not blocking:**
- `HexSignDet/Produce.lean:15-18` still says the diagnostics expose "unproved producer obligations" that "must eventually be excluded". This line is a hit for the Phase-2 keyword grep (`eventual`), and it is now false: `determinePrepared_success` and `buildPrepared_complete` exist.
- `HexSignDet/SPEC/hex-sign-det.md:20-22` lists `HexRowReduceTheory` as a companion import. No companion module imports it, and neither `libraries.yml:644` nor the companion SPEC lists it.

## Checked and found sound

- **Name coverage.** Every declaration in the companion SPEC's headline table exists with the stated shape. The new corollaries state the semantic conclusions, not literal certificate equality:
  - `determine_convert_counts`, `determine_convert_isSome`, `convert_signAt`, `convert_compare`, `buildRoots_convert_*`;
  - `buildReencoding_isSome`, which pairs `Domain` with membership of the selected root.
- **`determine_correct`** gives `Domain ∧ ∀ word, count = card`, which is slightly stronger than the SPEC because `word` ranges over every `List Int`.
- **Fallback values.** Empty table, `eq`, `0` and returning the source descriptor are all SPEC-specified, and each has a proved unreachability theorem. They are not Phase-2 placeholders.
- **`Dag.mapNodes`** matches SPEC line 287: it preserves indices, children and root, and makes no acceptance claim.
- **`Codec.Descriptor`** matches SPEC lines 312-323 and is exported through the umbrella. `HexRealClosure/SignRequests.lean` and `SignEvidence.lean` consume it through public imports.
- **Banned constructs.** No `sorry`, `axiom`, `native_decide`, `implemented_by` or `@[extern]` in either library or the adapters. `check_named_admissions.py:300-318` scans the adapters, `conformance/HexSignDetTheory` and the probe root.
- **No companion conformance module.** `conformance/HexSignDetTheory/Conformance.lean` is correctly absent; it moved to `Diagnostics/`.

## Notes that don't block

- The declared proof-probe root now only re-exports Diagnostics theorems (`bench/HexSignDetTheory/ProofProbe/Replay.lean`, `Nested.lean`). That's acceptable, since the proof track carries no timing obligation and the axiom guards apply transitively. But the root itself does no kernel work, so any future proof-cost observation of it would measure nothing.
- `Diagnostics/RootSemantics.lean` does not guard `convert_success` directly. Most other unlisted names are covered because guarded theorems depend on them.

## Recording format

Follow the pattern of `status/hex-sturm-theory.scaffolding-reviewed`: two separate tokens, `status/hex-sign-det.scaffolding-reviewed` and `status/hex-sign-det-theory.scaffolding-reviewed`. Each should give the source SHA, the owning SPEC path and the review scope, point to a retained findings file under `status/reviews/issue-10377-*.md`, and say that Phase 4 is not attested. Each library also gets its own `done_through: 2` in `libraries.yml`.
