# Phase 4/5/6 checkpoint 63

Scope: checkpoint for the **16 PRs merged** after summarize issue #8114 (sixty-second
checkpoint, closed 2026-06-19T22:33:53Z) — the window running from #8117 through #8149,
at HEAD `8bc6297f`. Two threads dominate, both polish rather than correctness. First,
the **Phase 6 grind-automation sweep reached its tail** across the computational
libraries: the last clusters of equation- and `↔`-shaped public `@[simp]` lemmas were
promoted to `@[simp, grind =]` (annotation-only), and two audit PRs (#8117, #8149)
confirmed the sweep is now essentially exhausted — the remaining bare `@[simp]` lemmas
all match documented-exclusion patterns. Second, the **first Phase 7 reference chapters
landed**: HexManual gained Verso chapters for HexPoly, HexModArithMathlib, and
HexGFqMathlib.

This window contains **no correctness movement**. The repository holds at **2 genuine
`sorry`s** (unchanged from checkpoint 62), both capstone-gated on the HO-1 / directive
#2564 chain, which remains open and blocked. The headline `sorry` reduction was the
previous window's work (checkpoint 62: 12→0 in HexGF2Mathlib/Field.lean). Checkpoint 63
is a proof-automation-and-documentation window, not a correctness window.

## Landed work

16 PRs merged after checkpoint 62 (#8117–#8149). Grouped by theme.

### Phase 6 grind-automation sweep — tail and audits (dominant by PR count)

Promotion of equation- and `↔`-shaped public `@[simp]` lemmas to `@[simp, grind =]` so
`grind` can E-match them, leaving `<`/`≤`/`Ne`/`∧`/`Associated`/`let`-binder shapes and
documented design-exclusions as `@[simp]`-only. Annotation-only; each promoted rule
strictly reduces RHS term structure (or is a known-terminating recursion), so it cannot
loop.

- **`*Mathlib` bridge layers** (merge-gating via `ci.yml`). HexMatrixMathlib/
  RankSpanNullspace (#8120), HexGFqMathlib/GF2q (#8122), HexBerlekampZassenhausMathlib
  Basic + LiftBridge (#8125), HexGFqField div_eq_mul_inv cross-layer parity (#8145).
- **Executable libraries.** HexGF2/Field Newton-interpolation cluster (#8130) and GF2n
  enumeration cluster (#8136), HexBerlekampZassenhaus/Basic (#8134), HexModArith/Ring
  arithmetic-identity cluster (#8137), HexGF2 Basic + Irreducibility missed equation
  lemmas (#8140), HexMatrix Determinant/Basic column-construction cluster (#8142),
  HexHensel/Basic modP_reduceModPow (#8143).
- **Audits.** #8117 audited the completed whole-sweep and applied one missed-sibling
  fix. #8149 (closing #8146) audited the post-#8117 incremental batch: it promoted the
  one genuine miss — HexGF2/Field `mem_rootsOfCoeffList` (an `↔`-shaped membership
  characterization, wrongly skipped as "Iff" by #8136; `grind =` accepts `Iff`) — and
  confirmed three exclusion clusters are deliberate (see below).

#8137 is worth singling out for the next planner: it promoted only **three** of nine
candidate ZMod64 identity lemmas (`add_zero`, `zero_add`, `pow_succ`) and deliberately
left **six** (`mul_zero`, `zero_mul`, `mul_one`, `one_mul`, `pow_zero`, `pow_one`)
`@[simp]`-only, because `ZMod64` carries a `Lean.Grind.Semiring` instance whose ring
normalizer collapses each LHS to a ground term or bare variable, leaving no usable
E-matching pattern (and grind already discharges these from the Semiring instance). This
exclusion is documented in the #8137 commit message and reaffirmed by the #8149 audit.

### Phase 7 reference chapters begin

The first Phase 7 work (HexManual Verso reference chapters) landed:

- HexPoly (#8127) — chapter written, `done_through` bumped 6→**7**.
- HexModArithMathlib (#8131) — chapter written. **`done_through` remains 6**: the PR
  title says "HexManual reference chapter" only and, unlike #8127/#8147, carries no
  counter-bump clause. The chapter exists in `HexManual/Chapters/`, but the library is
  not yet flagged fully done. A successor should either land the bump or record why it
  was held.
- HexGFqMathlib (#8147) — chapter written, `done_through` bumped 6→**7**.

`HexManual/Chapters/` now carries `HexPoly`, `HexGFqRing`, `HexGFqMathlib`, and
`HexModArithMathlib`.

## Quality metrics

Recomputed authoritatively at HEAD `8bc6297f` (not the planner snapshot):

- `sorry`: **2 genuine declarations** — unchanged from checkpoint 62. A raw
  `git grep -nw sorry -- '*.lean'` reports 5 lines; three are comment/docstring mentions
  (`HexBerlekampZassenhausMathlib/Basic.lean:231`, `.../IntReductionMod.lean:1288`,
  `HexMatrixMathlib/Determinant.lean:24`). The two real ones, both in tactic position
  and both capstone-gated on directive #2564:
  - `HexBerlekampZassenhausMathlib/Basic.lean:235` — `Hex.ZPoly.isIrreducible_iff`
    (C1 obligation; #4818 directive chain, tracked by #4170/#4819).
  - `HexBerlekampZassenhausMathlib/FactorSoundness.lean:20` —
    `factor_irreducible_of_nonUnit` (#8068, behind #6779).
- `axiom`: **0** real declarations (`git grep -nE '^[[:space:]]*axiom ' -- '*.lean'`
  empty).
- `native_decide`: **0** real uses (2 raw matches are comment mentions only).

## Limitations and honest framing

- **No correctness progress this window.** The HO-1 headline correctness theorem is not
  discharged. Both genuine `sorry`s are the directive #2564 (BZ van Hoeij CLD rewrite)
  correctness gap and have not moved. Directive #2564 is **open and blocked**, and its
  dependent chain is fully gated:
  - #6779 (B-builder — BadVectorBridge / B8 separation over L′ minus W) — blocked on
    #2564.
  - #4818 (executable ZPoly `isIrreducible_iff`) — blocked on #2564.
  - #8068 (close default factor irreducibility from raw branch proofs) — blocked on
    #6779.
- **The grind sweep is annotation-only polish**, not new verified content. It changes
  which lemmas `grind` can find, not what is proved.
- **The clean grind-sweep targets are exhausted.** The two issues the checkpoint-62
  planner flagged as remaining clean targets have since been overtaken by the #8149
  audit:
  - #8153 (HexGF2/Field `frobeniusIter` + `mem_rootsOfCoeffList`) is now largely stale:
    `mem_rootsOfCoeffList` was promoted by #8149, and the four `frobeniusIter_*` lemmas
    were *deliberately excluded* by the #8149 audit (the cluster is driven by forward
    `@[grind =>]` lemmas, and `frobeniusIter_succ`'s term-doubling shape risks
    E-matching blowup). Flagged on the issue; recommend close/skip rather than promotion.
  - #8156 (HexModArith/Ring mul/pow identity cluster) rested on a false "missed cluster"
    premise — those six are the #8137 documented Semiring-normalizer exclusions; skipped
    to `replan` with evidence.
  - #8151 (HexPolyZ/Basic `ratPolyPow` pair) remains a genuine open target (in-flight as
    PR #8155).

## Frontier

- Open PRs at checkpoint: #8155 (HexPolyZ/Basic `ratPolyPow` grind pair), #8152
  (HexModArith/Basic values-enumeration grind cluster), #2656 (spec hex-real-roots /
  hex-sturm, status planned).
- Next: land the HexModArithMathlib `done_through` 6→7 bump (or document the hold);
  continue Phase 7 reference chapters for the remaining libraries; close out #8153 as
  resolved-by-audit. The strategic blocker remains directive #2564 — no grind/Phase 7
  polish advances the HO-1 correctness gap.
