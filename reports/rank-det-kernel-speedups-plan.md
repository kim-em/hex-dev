# Plan: rank and det tactic speedups after Mathlib PR #43438

Four independent findings from profiling the Hex `rank` and `det` tactics
against Mathlib's `eval_rank` (master and the open PR
https://github.com/leanprover-community/mathlib4/pull/43438
feat(Tactic/Echelon): add per-model entry certifiers and support entries
settled by `norm_num`). Measurements are single runs on the shared host at
the sizes in `scripts/bench/{rank,det}_tactic_size_sweep.py`; the probe
files are under `/tmp/mathlib-tactic-perf`.

| Hex `rank`, full rank n=40 | today | PR 1 | + PR 2 | + PR 3a (packing on) |
|---|---|---|---|---|
| elaborator side | 1.7 s | 0.2 s | 0.2 s | 0.2 s |
| kernel | 1.6 s | 1.6 s | 0.8 s | 0.12 s |
| PR #43438 `eval_rank`, whole proof | 2.6 s | | | |

| Hex `det`, dense n=40 | today | PR 1 | + PR 2 | + PR 3b (packing on) |
|---|---|---|---|---|
| elaborator side | 3.0 s | 0.03 s | 0.03 s | 0.03 s |
| kernel | 3.0 s | 3.0 s | 2.1 s | 0.56 s |

Each PR carries its SPEC change and its implementation together, so the
SPEC never describes code that is not on `main` and `main` never has
behaviour the SPEC does not require. Order: PR 1, PR 2 and PR 4 are
independent of each other and can proceed in parallel worktrees; PR 3a
and PR 3b build on PR 2 and are optional at run time: the plain checkers
of PR 2 remain the certificate, and packing is an evaluation strategy
selected through the tactics' configuration structure (`rank -packing`,
`det -packing`), never through an option.

## Merge protocol, every PR

1. Branch from `main` in a fresh `git worktree`; commit with the session
   attribution lines; push to `origin` (kim-em/hex-dev); open the PR as
   soon as it compiles, title `perf(rank): …` / `perf(bareiss): …`, body
   in the "This PR …" style.
2. `lake build` of the touched libraries plus their `*Tests` libs, the
   `conformance/` sub-project targets for HexRank and HexBareiss, and the
   Mathlib layers (`HexRankMathlib`, `HexBareissMathlib`), which are
   merge-gating in CI.
3. Before/after measurement on adjacent arms, alternating `AB`/`BA`, per
   `SPEC/benchmarking.md`: the two tactic-size sweeps for the tactic-level
   PRs and the fresh-module probes under `bench/HexRankMathlib/ProofProbe`
   for the kernel-share numbers the SPEC quotes. Re-record
   `reports/bench-results/hex-{rank,bareiss}-mathlib-tactic-size-*.json`,
   regenerate `reports/figures/hex-{rank,bareiss}-mathlib-tactic-size.svg`
   with `scripts/plots/`, and update the numbers the SPECs state.
4. Second opinion: `~/.claude/skills/second-opinion/codex-opinion` on the
   diff, with the SPEC sections and the measurement as context; address
   what it finds.
5. CI `build` green, then `gh pr merge --squash`. Do not run the release
   sync.

## PR 1: add the proof without the elaborator re-check

**Finding.** Both tactics end with `mkAuxTheorem target proof`. With the
default `zetaDelta := false`, `Closure.mkValueTypeClosure` calls
`Meta.check` on the proof, which re-evaluates the `decide` certificate in
the elaborator. That is the whole "tactic execution" bar: 1.5 s for `rank`
and 3.0 s for `det` at n=40, equal to the kernel time each. Passing
`(zetaDelta := true)` was measured end to end in this worktree:

| case | today | after |
|---|---|---|
| `rank` full n=32 / n=40 | 2.0 / 3.4 s | 1.1 / 1.9 s |
| `rank` rank 2, n=128 | 7.8 s | 4.6 s |
| `det` dense n=40 | 6.3 s | 3.3 s |
| `det` singular n=40 | 2.1 s | 1.2 s |

**Change.** In `HexRankMathlib/Tactic.lean` and
`HexBareissMathlib/Tactic.lean`, replace `mkAuxTheorem target proof` by
`mkAuxLemma` on the closed target and proof, as `decide +kernel` does,
with the level parameters collected from the target. The target is
already required to be closed by `classify`, so no closure is needed. The
`try … catch` around it keeps delivering the kernel error to `diagnose`.

**SPEC.** `SPEC/matrix-tactics.md` §"The proof is assembled as one
auxiliary theorem": state that the lemma is added directly on the closed
proof and that `mkAuxTheorem`'s closure would type-check the proof in the
elaborator first, doubling the cost. Same sentence in
`HexRankMathlib/SPEC/hex-rank-mathlib.md` §The `rank` tactic and in
`HexBareissMathlib/SPEC/hex-bareiss-mathlib.md` (two places). Update the
tactic-size numbers those SPECs quote.

**Tests.** Existing `HexRankMathlib/Tests.lean` and
`HexBareissMathlib/Tests.lean`, including the false-target and
producer-bug diagnostics.

**Size.** About ten lines of code; an hour including the sweeps.

## PR 2: one-pass reads in the kernel checkers

**Finding.** `block` (rank lower bound) and `columns` (det) read every
entry with `nthRow`/`nthInt`, so extracting an r×r block costs about r³
list steps, the same order as the arithmetic. Kernel time at n=40:

| piece | today | one pass |
|---|---|---|
| rank `lowerCheck` including block extraction | 1459 ms | 767 ms |
| det `triangularCheck` including transpose | 2999 ms | 2106 ms |
| det singular `zeroDots` including transpose | 862 ms | 159 ms |

**Change, `HexRank/Kernel.lean`.** Replace `block` by a walk of each pivot
row once against the increasing column list (`pickCols`: at column index
`k`, take the entry when `k` is the next wanted column). Add
`strictInc c.cols` to `checkRankList`: the SPEC already says the columns
are increasing, the checker did not verify it, and the one-pass read
relies on it. `HexRankMathlib/Kernel.lean`: restate `block_length` and
`block_getElem` for the new definition (proof by induction on the row,
using the strictly increasing hypothesis).

**Change, `HexBareiss/Kernel.lean`.** Replace `columns` by a structural
transpose: fold the rows with a zip-cons into `m` initially empty
columns. `HexBareissMathlib/Kernel.lean`: restate `columns_length` and
`columns_getD` for it (induction on the rows, using `rowsLen`). Both
branches of `checkDetList` and `checkDetRat` inherit it.

**SPEC.** `HexRank/SPEC/hex-rank.md` §The kernel certificate: check 1
gains "cols strictly increasing"; the kernel-discipline paragraph says the
block is read in one pass per pivot row, no per-entry indexed read; the
cost paragraph replaces "`rank²` reductions of block entries" with
"`rank · m` steps of extraction". `HexBareiss/SPEC/hex-bareiss.md` §The
kernel certificate: "transposes the arranged matrix once (`columns`)"
becomes the one-pass fold, `n²` steps.

**Conformance.** Add a refuted witness with `cols := [1, 0]` to
`conformance/HexRank/Conformance.lean`; the existing replay and
refutation examples stay.

**Size.** About 40 lines of definitions and 80 of proofs; half a day.

## PR 3: Kronecker-packed dot products, as an optional evaluation strategy

Packing is not a new certificate. The plain checkers of PR 2 remain the
certificate semantics that the SPECs, the conformance replays and any
comparison with Mathlib refer to; the witness type does not change. Each
packed checker is a second function proven equal to the plain one as a
`Bool` under a no-overflow bound, and the tactics select it through a
configuration structure in the style of `decide +kernel`: a shared
`HexMatrixMathlib.KernelConfig` with `packing : Bool := true`, declared
with `declare_config_elab`, and the syntax `rank optConfig` /
`det optConfig`, so `rank -packing` and `det -packing` take the plain
path. The term form `det%` takes the same structure as a named argument;
the simproc `hex_norm_det` uses the defaults. With packing off the proof
term is exactly the PR 2 one. The tactic-size sweeps record a third
arm, `rank`/`det` with packing off, so the figures separate "same
certificate, packed versus unpacked" from "Hex certificate versus Echelon
certificate", and the plain path stays measured.

### PR 3a: rank lower bound

**Finding.** The lower bound does r³/3 multiply-adds of residues below the
modulus, at about 33 µs per term in the kernel. Packing a row into one
`Nat` with `W`-bit slots makes each dot product one GMP multiplication,
one shift and one mask, all kernel-accelerated. Prototype, block rows and
V columns packed by the kernel from the existing witness:

| rank lower-bound check | n=40 | n=64 |
|---|---|---|
| after PR 2 | 767 ms | 3403 ms |
| packed | 119 ms | 381 ms |

**Change, `HexRank/Kernel.lean`.** `packRow W`, `dotPacked W r pb pc :=
(pb * pc >>> (W * (r - 1))) &&& (2^W - 1)`, `lowerCheckPacked W` on packed
rows of the block against packed, zero-padded, reversed columns of `vt`,
and `checkRankListPacked W n m A c` differing from `checkRankList` only in
the lower-bound call and in checking `r * M² < 2^W`. `W` is a parameter
the tactic computes natively from the modulus and the rank (128 for the
first modulus, 256 for the last, 2⁸⁹ − 1). Witness and producer unchanged.

**Soundness, `HexRankMathlib/Kernel.lean`.** One lemma,
`dotPacked W r (packRow W b) (packRow W (reverse (pad r c))) = dotNat b c`
when all entries are below `2^k` and `r * 2^(2k) < 2^W`: `packRow` is
evaluation of the coefficient list at `2^W`, the coefficient of `X^(r-1)`
in the product is the dot product, and the bound makes the shift-and-mask
extraction exact. From it, `lowerCheckPacked W M B V = lowerCheck M B V`
and `checkRankListPacked W … = true → checkRankList … = true`, so
`rank_eq_of_checkListPacked'` is the existing theorem after a rewrite.

**Tactic.** `HexRankMathlib/Tactic.lean` elaborates the configuration,
computes `W` when packing is on, and applies the packed or the plain
theorem; `diagnose` evaluates the checker actually used. The
configuration structure and its `optConfig` syntax are introduced here,
in `HexMatrixMathlib`, so `det` reuses them in PR 3b.

**SPEC.** `HexRank/SPEC/hex-rank.md` §The kernel certificate gains a
subsection "Packed evaluation": the equality to the plain checker, the
bound, the cost (`r²/2` big multiplications of `r · W`-bit numbers plus
`r²` shift-adds), and the permitted primitives `Nat.shiftLeft`,
`Nat.shiftRight`, `Nat.land`. `HexRankMathlib/SPEC/hex-rank-mathlib.md`
§Kernel certificate lists the packing lemma; §The `rank` tactic documents
the configuration. `SPEC/matrix-tactics.md` records the shared
configuration structure and the rule that tactics are configured only
through it, not through options.

**Conformance.** Replay every existing witness through both checkers;
add a replay at the 2⁸⁹ − 1 modulus and a refutation with `W` too small.

**Size.** The lemma is the work; one to two days.

### PR 3b: det check and rank upper bound, signed entries

**Finding.** `triangularCheck` does about n³/6 multiply-adds of signed
minors (315 bits at n=40), and `rowsCheck` does `(n − r) · r · m` signed
`Int` multiply-adds (1.7 s at rank n/2, n=40). Prototype with each row
packed as a (positive part, negative part) pair and four products per
dot product:

| det dense n=40 | ms |
|---|---|
| after PR 2 | 2106 |
| packed, arithmetic only | 199 |
| packed, kernel also packs the rows and columns | 559 |

The singular branch gains nothing from packing after PR 2 (159 ms
unpacked against 261 ms packed) and is shared by both checkers.

**Change.** `HexBareiss/Kernel.lean`: `packPair W`, `dotP W r` with four
`dotPacked` products and an `Int` subtraction, `triangularCheckPacked W`
and `checkDetListPacked W n A c`, which additionally verifies every
transform and matrix entry has `natAbs` below `2^k` and `n * 2^(2k) < 2^W`.
`HexRank/Kernel.lean`: `rowsCheckPacked W`, the same identity stated as
`denom • a = z · Pᵀ` entrywise. `W` is computed by the tactic from the
entries and passed as a parameter; the witnesses are unchanged.

**Soundness.** The signed lemma is the unsigned one of PR 3a applied four
times to `(t⁺ − t⁻) · (c⁺ − c⁻)`; then `triangularCheckPacked W … =
triangularCheck …` and `rowsCheckPacked W … = rowsCheck …` under the
bounds, and the packed theorems are the plain ones after a rewrite.

**SPEC.** "Packed evaluation" subsections in `HexBareiss/SPEC/hex-bareiss.md`
and the check-3 paragraph of `HexRank/SPEC/hex-rank.md`; the Mathlib SPECs'
bridge-lemma lists and the configuration in the `det` tactic section.

**Conformance.** Both checkers on every existing witness; refutations for
a too-small `W` and for an entry above the declared bound.

**Size.** One to two days on top of PR 3a.

## PR 4: producer in O(r³) modular arithmetic

**Finding.** `witnessData` runs `rowReduceFF (augmentIdentity B_k)` for
every leading pivot block, O(r⁴) fraction-free operations over `Int`, to
get the columns of `V`. It is 0.19 s at n=40 but the fastest-growing
native cost (about 1.3 s at n=64 by extrapolation).

**Change, `HexRank/Kernel.lean`.** Column `j` of `V` is `B_j⁻¹ e_j` modulo
`M`, so compute it by one LU factorisation of the pivot block modulo `M`
(O(r³) word operations, the leading minors are units by the same
condition the retry loop already enforces) and back substitution per
column. The integer adjugate of the full block, which the upper bound's
`z` rows need, stays as it is. The witness values are unchanged, since
`V` is uniquely determined, so fixtures and tests do not move; the
producer self-check remains the soundness backstop.

**SPEC.** `HexRank/SPEC/hex-rank.md` §The kernel certificate, producer
paragraph, and the `rankWitness` row of the Complexity table
(`O(r⁴ + (n − r) · r²)` becomes `O(r³ + (n − r) · r²)` with `r³` modular
word operations).

**Size.** Half a day; measured through the `witness` phase of the tactic
before and after.

## Out of scope

Elaboration of the literal and `norm_num` on its entries (3.5 s of the
4.6 s at rank 2, n=128 after PR 1) happen before the tactic runs and are
not addressed here. The tactic-size sweep scripts could take `--root` and
`--tools` options to run against a Mathlib checkout directly; useful, but
a separate change.
