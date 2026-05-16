## Current state

PR #4505 (merged commit `cceba604`) landed the mask-level helper
`subsetSplits_prefix_exists_bit_diff_aux` as partial progress on #4504. The
helper sits at `HexBerlekampZassenhausMathlib/Basic.lean:2813` and spans
~326 lines through line 3139, immediately before
`liftedSubsetSplit_prefix_mem_of_matches` (line 3140).

It is the inductive structural core of the matched-state prefix-with-bit-
difference lemma. Signature:

```lean
private theorem subsetSplits_prefix_exists_bit_diff_aux
    {xs : List Hex.ZPoly} (hxs_nodup : xs.Nodup)
    {mask_S mask_T : List Bool}
    (hSlen : mask_S.length = xs.length)
    (hTlen : mask_T.length = xs.length)
    {pre suffix : List (List Hex.ZPoly × List Hex.ZPoly)}
    (hsplits :
      Hex.subsetSplits xs =
        pre ++
          ((xs.zip mask_S).filterMap (fun p => if p.2 then some p.1 else none),
           (xs.zip mask_S).filterMap (fun p => if p.2 then none else some p.1))
            :: suffix)
    (hT_in_pre :
      ((xs.zip mask_T).filterMap (fun p => if p.2 then some p.1 else none),
       (xs.zip mask_T).filterMap (fun p => if p.2 then none else some p.1))
         ∈ pre) :
    ∃ i, ∃ hi : i < xs.length,
      mask_T[i]'(hTlen ▸ hi) = false ∧
      mask_S[i]'(hSlen ▸ hi) = true
```

Per the session progress note (`progress/20260516T151038Z_3f1d8d64.md`),
the proof is direct induction on `xs` with case splits on
`(mask_S.head, mask_T.head)`:

- `(true, false)` immediate at `i = 0`.
- `(false, true)` impossible: shape rules out the natural L_false/L_true
  partition under `x ∉ xs'` (uses `hxs_nodup`).
- `(true, true)` / `(false, false)` recurse on the tail after lifting the
  L_true / L_false structure equation back to `subsetSplits xs'` via
  `List.map_eq_append_iff`.

The helper is currently `private` and has no consumer; the matched-state
wrapper `liftedSubsetSplit_prefix_exists_mem_sdiff_of_matches` that calls
it is the open feature #4508. The helper must be sound on its own before
#4508's wrapper lands and starts depending on its conclusion.

## Deliverables

A focused review pass on `subsetSplits_prefix_exists_bit_diff_aux` (lines
2813–3139 of `HexBerlekampZassenhausMathlib/Basic.lean`). Concretely:

1. Verify the `xs.Nodup` hypothesis is genuinely load-bearing in the
   `(false, true)` impossibility branch. If the impossibility argument
   does not actually use `hxs_nodup`, either drop the hypothesis or
   make the dependence explicit. If it does use it, confirm the
   argument's appeal to `x ∉ xs'` is via `List.Nodup.cons` or
   `List.nodup_cons` rather than a stronger fact that could be weakened.

2. Verify the case analysis on `(mask_S.head, mask_T.head)` is
   exhaustive and that none of the four cases is silently using
   `omega` / `decide` to mask a missed subcase. The expected pattern
   is direct `rcases mask_S with _ | ⟨b, msS⟩` followed by symmetric
   `rcases mask_T` and a `match` / `cases` on the two heads.

3. Verify the recursive cases lift the L_true / L_false structure
   equation back to `Hex.subsetSplits xs'` via `List.map_eq_append_iff`
   correctly: in particular that the resulting `pre` on the tail still
   contains the tail's mask-T split as a member, so the induction
   hypothesis applies with `hT_in_pre`-shaped tail premise. The index
   bump `i ↦ i + 1` on recursion must match the `(b :: msS)` /
   `(b :: msT)` head extension.

4. Confirm there are no `sorry`, `axiom`, `native_decide`, `TODO`, or
   `FIXME` introduced in the helper. (The file's running sorry count
   should be unchanged by PR #4505; verify against `master`.)

5. Tactic-style and minimality pass following the project convention
   (see [`.claude/CLAUDE.md`](.claude/CLAUDE.md) "Proof Cleanup and
   Maintenance" guidance from `~/.claude/CLAUDE.md`): combine adjacent
   `rw` / `simp` steps where it does not obscure the proof, and remove
   any step that turns out to be redundant once an earlier step
   normalises the goal.

6. If you find a fix or simplification, apply it in this PR; the
   helper has no current consumer (#4508 is still open), so the
   review is the right time to refine the signature or proof before
   downstream callers exist. If the helper's signature changes,
   leave a short comment in #4508 so the wrapper plan tracks the
   change.

## Out of scope

- The top-level wrapper `liftedSubsetSplit_prefix_exists_mem_sdiff_of_matches`
  itself (that is #4508).
- The matched-state forward bridge `liftedSubsetSplit_prefix_mem_of_matches`
  immediately downstream of the helper (already merged separately).
- Any restructuring of `Hex.subsetSplits` itself in `HexBerlekampZassenhaus`
  core.
- Editing `SPEC/`, top-level `PLAN.md`, or top-level `.claude/CLAUDE.md`.

## Verification

- `lake build HexBerlekampZassenhausMathlib.Basic`
- `lake build HexBerlekampZassenhausMathlib`
- `python3 scripts/check_dag.py`
- `git diff --check`
- Sorry / axiom / `native_decide` counts unchanged or reduced in
  `HexBerlekampZassenhausMathlib/Basic.lean` relative to `origin/main`.
- If no changes are warranted, post a review comment on the issue
  summarising what was checked and close the PR as
  "review-only, no fixup needed" (or close the issue without a PR if
  the review surfaced nothing actionable; the worker flow allows this).

## Context

- PR #4505 — `feat: add mask-level subsetSplits prefix bit-diff helper
  (#4504 partial)` (merged `cceba604`).
- #4504 — the parent feature issue, now closed.
- #4508 — the open follow-up wrapper that will consume this helper.
- Recent precedent for focused reviews of newly-landed proof clusters:
  #4502 (review of #4497 capstone), #4496 (review of HexGfqRing
  Phase 6 binary-decomposition bridge), #4489 / #4490 (review of
  HexGfqRing pow / Lean.Grind clusters).
