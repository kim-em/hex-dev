# Independent conformance-repair review

The repair itself is sound, and I found nothing blocking. The Lean change introduces no weakening, admissions or semantic change. My findings are about provenance, scope and evidence wording, all Low or Info.

## The Lean repair

- **Same file as main.** The file at HEAD is byte-identical to the version on `origin/main`, on PR #10632's head `81c736a2`, and in `990282187` (#10641). All four share blob `776f0924`.
- **`partialRaw` is unchanged.** The removed `GraphSignsConformance` defined it as `{singletonRaw with indices := [1], signs := [1]}`, and the new local definition is identical. Its only users are `siblingsPass` and `headMismatchPass`, and both `#guard`s still run. Nothing else referenced the old name; the `partialRaw` in `FieldChecks.lean:454` is a local `let`.
- **No other names change meaning.** The parent opened both `GraphSignsConformance` and `CoefficientSignsConformance`, and both define `source` and `source_raw` the same way (from `singletonRaw` via `Descriptor.ofTable`). Now only `CoefficientSignsConformance` supplies them, so `leafMemo`, `query_eq` and `readFact` see the same terms. `selected_kernel` is still the file's own theorem.
- **No new admission exposure.** The added non-meta `public import HexSignDet.CrossCheck` matches main. `conformance/HexSignDet/CrossCheck.lean` contains no `sorry`, `axiom`, `admit`, `implemented_by`, `extern` or `unsafe`.
- **No theorem was touched.** All three `#print axioms` guards are unchanged and still pin `[propext, Classical.choice, Quot.sound]`. `literal_fact_kernel`, `selected_kernel` and `nestedPass` are unchanged.

## Findings

**1. Low (scope and provenance): the repair is already on main, so rebase instead of carrying a copy.**
- **Where:** `conformance/HexRealClosureMathlib/SignFactsConformance.lean`, and `owner_repair` in `reports/bench-results/prerequisite-rebase-verification.json`.
- **Issue:** the identical change landed on main in `990282187` (#10641), and #10632 (`9498f1e2d`) doesn't touch the file. The branch's base `293d981ea` is just before both. So this PR carries a main-owned fix, against the "PR Scope" rule, and the evidence says the fix was copied from #10632 when on main it actually came from #10641.
- **Fix:** rebase onto `origin/main` (at or after `990282187`). The Lean hunk then drops out of the PR diff. Point `owner_repair` at the main commit `990282187` instead of the PR head `81c736a2`, and re-run the admission scan and conformance build on the rebased head. Merging as-is would not conflict, since the content is identical; this is about a clean diff and accurate provenance.

**2. Low (evidence provenance): the passing results don't say which tree they ran on.**
- **Where:** `prerequisite-rebase-verification.json`. The top-level `source_commit` is `63bc716` (the broken tree), but `owner_repair.{full_conformance_build, named_admission_scan, fresh_exact_oracle}` were measured on the uncommitted tree that became `33e12a7f9`.
- **Risk:** a reader can attribute the passing scan to `63bc716`, or can't tell which tree passed at all.
- **Fix:** add `"measured_on": "working tree of the commit adding this file"`, or record the tree hash. Better, once rebased, record the rebased HEAD and the green CI run URL in a follow-up.

**3. Low (misleading grouping): `fresh_exact_oracle` sits under `owner_repair`.**
- **Issue:** this places "83 cases, fixture byte match" inside the block describing the `SignFactsConformance` repair. Those oracle cases exercise the owned libraries' fixtures, not this file. The file is validated only by its `#guard`s and kernel proofs during the conformance build.
- **Fix:** move `fresh_exact_oracle` into `local`, or add a `"covers"` field naming the libraries, so it doesn't read as evidence for the repair.

**4. Low (artifact honesty): the `.log` file is not a log.**
- **Where:** `reports/bench-results/prerequisite-rebase-admission-failure.log` is one paraphrased line, not output from `check_named_admissions.py`.
- **Fix:** commit the scanner's actual stderr, or delete the file and keep the reason in the JSON (which already has it). Calling a one-line summary a `.log` overstates it.

**5. Info: the 217 s / 36 s figures are unverified here.**
- **Confirmed via `gh`:** run 37119197374 is on `63bc716` and failed only at "Check dependency DAG and trusted-internals imports". That step runs `check_dag.py` and then `check_named_admissions.py` (`ci.yml:121-126`), which matches the JSON's `dag_check: success` alongside the admission failure. Run 36983780557 succeeded on `04c922403`.
- **Not checked:** I couldn't pull that run's log, so I didn't check the 217 s total or the 36 s for this executable.
- **Wording is fine:** the report labels both timings as historical and says they don't establish headroom on the current base.
- **Small gap:** the report sends readers to the rebase evidence JSON for "the rebased verification". That JSON has no bench timing on the new base, only the failed run. Add "no bench-verify timing on the rebased base yet" so readers don't expect one.

**6. Info: a stale doc reference outside this commit.**
- `reports/real-closure-requirements.md:49` still lists `GraphSignsConformance` as an evidence module, but #10640 deleted it.
- That reference is main's to fix, not this PR's, unless the PR already edits that report.

## Phase claims

The commit doesn't touch phase claims. The evidence JSON's `scope` and the review note both still say Phase 3 only and Phase 4 incomplete, which is consistent. The CI-before-merge condition appears in both the JSON and the report.


## Response

The owner correction subsequently merged to main through #10641 and was also present in #10632’s reviewed head. The branch was rebased onto main commit 9498f1e2d, preserving both new field-sign conformance modules at their existing paths and registrations. No owner conformance or implementation hunk remains in the PR. Provenance now names the main correction commit and separates historical passing results on the tree that became 33e12a7f9 from the earlier failed 63bc71637 scan. The real-algebraic oracle result is grouped with local library evidence and names its scope. The report explicitly records that there is no completed rebased benchmark timing yet.

The one-line failure log is actual captured scanner stderr, not a paraphrase: the scanner catches ValueError and raises SystemExit with its string. Its bytes match the captured local failure. This finding requires no change. The historical CI log confirms 217 seconds total and 36 seconds for real-algebraic; these observations remain tied to their original source. The stale GraphSignsConformance reference is in a report this PR does not edit, and stays with its owner.
