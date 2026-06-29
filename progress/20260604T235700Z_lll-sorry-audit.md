# LLL sorry audit + planner drive

Interactive session (Kim): audit the LLL verification state, sanity-check
the issues, file/replan issues, drive via `pod once`.

## Accomplished

- Pulled stale checkout 1b1eb333 -> bd863862. The 6463 GramSchmidt sorry
  was already closed upstream (#6554). Revised inventory: 4 sorries remain.
- Difficulty + soundness assessment of all 4 (see below).
- Sanity-checked the issue cluster. Closed #6423/#6424/#6425 as superseded
  (abandoned QuotientProvider design; provider type 0 refs in live tree;
  deps #6381/#6374/#5655 closed). Replanned #6382 onto the StepWitness
  route (dropped dead provider framing + stale blocked/replan labels).
- Filed #6557 (mem_latticeSubmodule_iff) and #6558 (short-vector Step 1,
  GS-norm telescoping bound).
- Launched `pod once --type work` on #6557, #6558, #6382 (all claimed,
  running: agents 8961ddc4, 74338bd4, 5f43b57b).

## Current frontier

4 sorries:
1. HexLLL/Basic.lean:470 lllAux termination — UNSOUND as typed (lllAux is
   total but needs independence/positivity for swap-branch decrease;
   lllUnchecked + HexBerlekampZassenhaus consume the proof-free path).
   Design decision pending (fuel-refactor vs independence-thread vs defer).
   No `partial def` allowed in project (SPEC design-principles §8).
2. HexGramSchmidt/Int.lean:6158 gramDetVecEntry_eq_leadingPrefix_bareiss
   -> #6382 (driving).
3. HexLLLMathlib/Basic.lean:61 mem_latticeSubmodule_iff -> #6557 (driving).
4. HexLLLMathlib/Basic.lean:108 short-vector bound — docstring misleading;
   executable short-vector theorem does NOT exist. Step 2 done
   (normSq_latticeVec_ge_min_basis_normSq, Int.lean:7105); Step 1 -> #6558
   (driving); Step 3 + Mathlib transport = follow-on, blocked on #6558+#6557.

## Next step

- Monitor #6557/#6558/#6382 pods; merge green PRs; re-drive on failure.
- After #6558 lands, file short-vector Step 3 (executable lll_short_vector)
  then the transport issue (the actual :108 sorry, needs #6557 too).
- Resolve termination design decision with owner, then file accordingly.

## Blockers

- Termination sorry needs an owner design decision (totality vs
  independence vs fuel). #6440 is an owner `directive` largely satisfied by
  #6554 but has bench/report deliverables — flagged, not closed.
