# Independent owner-repair rebase review

I found no blockers in the rebase itself. Both `lakefile.lean` conflicts are resolved correctly, and the PR diff against `9498f1e2d` only touches files this branch owns. The real gap is in the attestation: this PR records `done_through: 3` for both real-algebraic libraries, and that now includes `signField`, which main added and no review on this issue has checked. The evidence JSON and the prerequisites report also have some provenance and staleness problems. I didn't build anything, and some read-only commands (for example writing comparison diffs to `/tmp`) were refused, so I compared file by file instead.

## What checks out

- **`lakefile.lean`:** the change from `33e12a7f9` to HEAD is byte-for-byte main's own change, and the branch's diff against `9498f1e2d` is identical to its pre-rebase diff against `293d981ea`.
  - Both `FieldSignConformance` modules (`HexRealAlgebraic` and `HexRealAlgebraicMathlib`) stay at their conformance paths and stay in the `HexConformance` glob list unchanged.
  - The `HexRealAlgebraicMathlib.Audit` glob was added in `3f692059b` and removed again in `e59d4acfb`, so every intermediate commit is consistent too.
  - `HexSturmMathlibTests`, `HexRealAlgebraicMathlibTests`, the two `HexQuerySemantics` replay modules, `HexSturmBenchSupport`, `hexrealalgebraic_bench` and the removal of the Sturm conformance/Replay globs are all intact.
- **Diff against `9498f1e2d`:** it contains only the four libraries' own files, their tests, bench and conformance files, reports, scripts and status files. `ci.yml`, `check_dag.py` and `libgraph.py` add only this branch's targets, and every upstream target list is preserved.
- **Diff against `33e12a7f9`:** it covers 63 files, which is exactly main's 64-file change minus `conformance/HexRealClosureMathlib/SignFactsConformance.lean`. That file is now identical to main, so the earlier fix really is inherited and no longer in your diff. The only file both sides changed besides the lakefile is `SPEC/Libraries/hex-real-algebraic.md`, and it merged cleanly.
- **Independence claim:** `prerequisites.md:46` says the real-algebraic operations don't depend on HexSturm, HexSignDet or HexRealClosure. That still holds, because `FieldSign.lean` only pulls in `HexNumberField.{Nearest,Convert,Roots}`.

## Findings

**1. Medium: `done_through: 3` now covers `signField`, which nothing on this issue has reviewed or declared**
- **Where:**
  - `libraries.yml` (HexRealAlgebraic and HexRealAlgebraicMathlib, 1→3)
  - `status/hex-real-algebraic{,-mathlib}.scaffolding-reviewed`
  - the module docstring of `conformance/HexRealAlgebraic/Conformance.lean`
  - the HexRealAlgebraic row in the table at `reports/real-closure-prerequisites.md:19`
- **Problem:** main added public API to both libraries: `HexRealAlgebraic/FieldSign.lean` (`signField`) and `HexRealAlgebraicMathlib/FieldSign.lean` (`signField_spec`, `signField_eq`), and the shared SPEC lists it.
  - The Phase-2 attestations name source commits `4f44b806` and `6d78bf3e1`, and their lists of implemented bodies don't include it.
  - PLAN/Phase3.md requires the conformance docstring to declare every public operation. The `Conformance.lean` docstring doesn't mention `signField`, nor that `FieldSignConformance` elaborates as part of this library's coverage.
  - The new paragraph at `prerequisites.md:39-44` only says the modules "remain registered". It doesn't show that the Phase-3 contract is met.
- **Fix:**
  - Add `signField` to the covered operations in the `Conformance.lean` docstring and point to `FieldSignConformance`. That module has 4 `#guard`s over 4 generators and checks against the canonical sign, so it is adequate coverage.
  - Add a short independent review addendum covering both `FieldSign.lean` files to each scaffolding token.
  - Add `signField` to the coverage column of the table.
  - Alternatively, explicitly exclude it from the attestation, but per-library phase records make that the weaker option.

**2. Low–Medium: the Verification section of `real-closure-prerequisites.md` describes an older rebase**
- **Where:** `real-closure-prerequisites.md:8-11` and `:99-105`.
- **Problem:**
  - Lines 99-105 cite "rebased full local build (15412 jobs)", 15051 jobs and 9824 jobs. Those predate both later rebases; the JSON records 15525 and 14772.
  - Lines 8-11 list "required PR CI" as Phase-3 evidence. The last required run on a rebased tree failed (37119197374), and the one for the current tree hasn't run yet.
  - The report never links `prerequisite-rebase-verification.json`.
- **Fix:** replace the job counts with a link to the JSON, and say that required CI on the final revision is pending until it passes.

**3. Low: the evidence JSON mixes three source trees, and none of them is the current one**
- **Where:** `reports/bench-results/prerequisite-rebase-verification.json`.
- **Problem:**
  - The top-level `source_commit`/`base_commit` are `63bc716` on `293d981ea`.
  - Several results are marked `measured_on` `33e12a7f9`, an old-base tree that carried its own copy of the fix and lacked #10641/#10632's other Lean changes.
  - The `rebased_on_owner_repair` block for `4a4dd07f9` on `9498f1e2d` has no results yet. Its "Required full CI pending" is honest, but it needs the local build, conformance and named-admission results once your runs finish.
  - The phrase "same Lean tree as its measured uncommitted predecessor" can't be checked by a reader. Something like "uncommitted working tree whose `*.lean` content equals `33e12a7f9`" would say what it means.
  - `required_ci` (the failed run) has no `source_commit`. The earlier owner-repair review confirmed it ran on `63bc716`.
  - `also_present_in_pr: #10632` is ambiguous, because the squash of #10632 (`9498f1e2d`) doesn't touch the file. Either say "on #10632's branch head `81c736a2`, landed via #10641", or drop the field.
  - After the force-push, `63bc716` and `33e12a7f9` won't be on any branch. Label them as pre-rebase SHAs.
  - If you amend the uncommitted edits into `4a4dd07f9`, the `rebased_on_owner_repair.source_commit` value becomes a dangling self-reference. Commit them separately, or record the hash after amending.
  - `"existing_owner_repair": "#10632 / #10641"` uses shorthand while the rest of the file uses full URLs.

**4. Low: one commit message and one review response no longer match the content**
- **Where:** commit `4a4dd07f9`, and `status/reviews/issue-10577-opus-rebase.md` (the "Response and verification" section).
- **Problem:**
  - The commit is titled "fix: repair conformance import after upstream module removal", but it now contains only reports, logs and a review file.
  - The response says "The exact conformance-only owner correction from PR #10632 is included". The correction is no longer in the diff, and it came from #10641.
- **Fix:** retitle the commit (for example `chore: record rebase verification evidence`) and correct that sentence. `issue-10577-opus-owner-repair.md` is still untracked, so remember to add it.

**5. Low (future release work): a library-directory test imports a conformance-only module**
- **Where:** `HexSturmMathlib/Tests/Replay/Accepted.lean`.
- **Problem:** it imports `HexSturm.Fixtures`, which lives under `conformance/`. The monorepo build is fine with that, but once hex-sturm-mathlib appears in `scripts/release/released.yml` (it isn't there yet), its mirror won't have that module.
- **Fix:** note it for the release work (#10575 or whichever issue owns publishing).

**6. Nit: vocabulary**
- The new text at `real-closure-prerequisites.md:44` says "scaling gate", and the existing `hex-real-algebraic-performance.md:32` says "smoke input". Both words are on your banned list; "required scaling check" and "fast check input" would work.

## Evidence wording

The evidence wording is otherwise honest:
- Both reports and the JSON scope say Phase 3 only and Phase 4 incomplete.
- The failed admission scan and the failed CI run are kept, with the reason.
- The `signField` row in the performance report correctly says the owner's evidence is a pre-refactoring binary (`7b2b23f7`) with no current-call scaling result and no Phase-4 pass, which matches `bench-results/field-sign/README.md`.
- The `fresh_exact_oracle` result is now correctly labelled as covering the real-algebraic fixture surface and not `SignFactsConformance`.

Still needed before merge: your in-flight local Lake, conformance and named-admission results recorded against `4a4dd07f9` on `9498f1e2d`, then green required CI on the final head.


## Response

The new field-sign operation is named in the core conformance coverage declaration and both matrix rows. Its existing field-sign tests and ordinary-kernel guards remain compiled at their original paths. A dedicated independent scaffolding review addendum is requested for both inherited modules; it is distinct from their incomplete Phase-4 performance evidence. The verification report now links the source-specific record rather than asserting older job counts as current. Required final CI is an explicit merge condition. The JSON separates pre-rebase failures/checks from checks on the current main base and names the correction commit #10641.

The split-package dependency on the conformance fixture module HexSturm.Fixtures is recorded for #10575. Source inspection confirms both lakefile conflict resolutions preserve upstream registrations. The intermediate evidence commit retains its source identity; the squash delivery title describes the final audit and implementation, rather than an inherited repair. The earlier one-line admission failure is the scanner’s actual SystemExit stderr, as confirmed in its source.
